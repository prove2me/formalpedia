-- Prove2me | solution 1 for SingleExpBisect.Main.dp_sparse_io_bit_budget
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:11:14.387523+00:00
-- url     : https://prove2.me/submissions/fd1a25fd-8cbd-4f23-9bc9-1c813963c474

import Mathlib
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical
namespace SingleExpBisect.Machine
open SingleExpBisect.Main MinBisectFPT ExponomialAssortment.FPTAS

private theorem naturalLength (n : ℕ) : (encodeNat n).length ≤ 2*n+1 := by
  have h : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simpa [encodeNat, ← Nat.size_eq_bits_len, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using Nat.add_le_add (Nat.add_le_add h h) (le_refl 1)

private theorem flatLength {α β : Type} (l : List α) (f : α → List β) (bound : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ bound) :
    (l.flatMap f).length ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    omega

theorem inputLength {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (encodeInput G k).length ≤ n*n + 2*n + 2*k + 2 := by
  classical
  have h := flatLength (List.finRange n)
    (fun u => (List.finRange n).map fun v => decide (G.Adj u v)) n (by simp)
  simp only [List.length_finRange] at h
  simp only [encodeInput, List.length_append]
  have hn := naturalLength n
  have hk := naturalLength k
  omega

theorem setLength {n : ℕ} (A : Finset (Fin n)) :
    (encodeSet A).length ≤ (n+1)*(2*n+1) := by
  classical
  let vertices := (List.finRange n).filter (· ∈ A)
  have h := flatLength vertices (fun v => encodeNat v.val) (2*n+1)
    (fun v _ => (naturalLength v.val).trans (by have hh := v.isLt; omega))
  have hv : vertices.length ≤ n := (List.length_filter_le _ _).trans_eq List.length_finRange
  have ha := naturalLength A.card
  have hc : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hm := Nat.mul_le_mul_right (2*n+1) hv
  change (encodeNat A.card ++ vertices.flatMap _).length ≤ _
  rw [List.length_append, Nat.succ_mul]
  omega

end SingleExpBisect.Machine

open scoped Classical
namespace SingleExpBisect.Machine
open SingleExpBisect.Main MinBisectFPT ExponomialAssortment.FPTAS

private theorem bitLength (n : ℕ) : (encodeNat n).length ≤ 2*n+1 := by
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simpa [encodeNat, ← Nat.size_eq_bits_len, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using Nat.add_le_add (Nat.add_le_add hn hn) (le_refl 1)

private theorem flatBound {α β : Type} (l : List α) (f : α → List β) (z : ℕ)
    (h : ∀ a, (f a).length ≤ z) : (l.flatMap f).length ≤ l.length*z := by
  induction l with
  | nil => simp
  | cons a l ih => simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add ih (h a)

/-- Size bound for the exact serialized decomposition in #803. -/
theorem treeLength {n : ℕ} (T : RootedTD n) :
    (encodeTD T).length ≤ (2*T.N+1) + T.N*((2*T.N+1) + (n+1)*(2*n+1)) := by
  classical
  have parent (t : Fin T.N) : (T.parent t).elim 0 (fun t' => t'.val+1) ≤ T.N := by
    cases hh : T.parent t with
    | none => exact Nat.zero_le _
    | some p => exact p.isLt
  have per (t : Fin T.N) :
      (encodeNat ((T.parent t).elim 0 fun t' => t'.val+1) ++ encodeSet (T.bag t)).length ≤
        (2*T.N+1)+(n+1)*(2*n+1) := by
    rw [List.length_append]
    have hh := bitLength ((T.parent t).elim 0 fun t' => t'.val+1)
    have hp := parent t
    exact Nat.add_le_add (by omega) (setLength _)
  rw [encodeTD,List.length_append]
  exact Nat.add_le_add (bitLength _) (by simpa only [List.length_finRange] using flatBound (List.finRange T.N) _ _ per)

theorem nodeBudget {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n)
    (valid : IsSec3Decomp G T k) (t : Fin T.N) : (nodeInput G k T t).length+1 ≤ stepBound 32 k n := by
  have num := valid.2.2.2.1
  have nodes : T.N ≤ n+1 := by omega
  have h := treeLength T
  have h1 : 2*T.N+1 ≤ 2*(n+1)+1 := by omega
  have h2 := Nat.mul_le_mul nodes (Nat.add_le_add_right h1 ((n+1)*(2*n+1)))
  have hx := inputLength G k
  have ht := bitLength t.val
  have it := t.isLt
  simp only [nodeInput,List.length_append]
  have major : n*n+2*n+2*k+2 + ((2*(n+1)+1)+(n+1)*((2*(n+1)+1)+(n+1)*(2*n+1))) +
      (2*(n+1)+1) + 1 ≤ 32*(2*k+1)*(n+1)^3 := by ring_nf; omega
  have he : 2*k+1 ≤ 2^(32*k) := by have he' : 32*k < 2^(32*k) := Nat.lt_two_pow_self; omega
  have hd : (n+1)^3 ≤ (n+1)^32 := Nat.pow_le_pow_right (by omega) (by decide)
  exact le_trans (by omega) (major.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 32 he) hd))

end SingleExpBisect.Machine

open scoped Classical
open SingleExpBisect.Main MinBisectFPT
set_option autoImplicit false
namespace SingleExpBisect.Machine
open ExponomialAssortment.FPTAS

private lemma rename_exponent {n : ℕ} (D A : Finset (Fin n)) (c : ℕ) :
    Finsupp.mapDomain (omegaVar D) (Finsupp.single Var.w c + yMono A) =
      Finsupp.single Var.x (A \ D).card + Finsupp.single Var.w c + yMono (A ∩ D) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [yMono,omegaVar,Finsupp.mapDomain_single]
  | insert i A hi ih =>
    have hs : yMono (insert i A) = Finsupp.single (Var.y i) 1 + yMono A := by simp [yMono,hi]
    rw [hs,add_left_comm,Finsupp.mapDomain_add,Finsupp.mapDomain_single,ih]
    by_cases hd : i ∈ D
    · have e : insert i A \ D = A \ D := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = insert i (A ∩ D) := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f]; simp [omegaVar,hd,yMono,hi,add_comm,add_left_comm,add_assoc]
    · have e : insert i A \ D = insert i (A \ D) := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = A ∩ D := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f,Finset.card_insert_of_notMem (by simp [hi]),Finsupp.single_add]
      simp only [omegaVar,if_neg hd]; abel

private lemma renamed_cut_support {n : ℕ} (G : SimpleGraph (Fin n)) (W D : Finset (Fin n)) (k : ℕ)
    (A : Finset (Finset (Fin n))) (hk : ∀ S ∈ A, mu G W S ≤ k) :
    let P := omega D (∑ S ∈ A, MvPolynomial.monomial (Finsupp.single Var.w (mu G W S) + yMono S) 1)
    P.support.card ≤ 2^D.card * (n+1) * (k+1) ∧
      (∀ e, ∃ j : ℕ, j ≤ 2^n ∧ MvPolynomial.coeff e P = (j : ℚ)) ∧
      ∀ e ∈ P.support, e Var.x ≤ n ∧ e Var.x' = 0 ∧ e Var.w ≤ k ∧ ∀ v, e (Var.y v) ≤ 1 := by
  classical
  dsimp only
  let exp := fun S : Finset (Fin n) => Finsupp.single Var.x (S \ D).card +
    Finsupp.single Var.w (mu G W S) + yMono (S ∩ D)
  let P := ∑ S ∈ A, MvPolynomial.monomial (exp S) (1:ℚ)
  have eq : omega D (∑ S ∈ A, MvPolynomial.monomial (Finsupp.single Var.w (mu G W S) + yMono S) 1) = P := by
    rw [map_sum]; apply Finset.sum_congr rfl;intro S hS
    change MvPolynomial.rename (omegaVar D) _ = _
    rw [MvPolynomial.rename_monomial,rename_exponent]
  rw [eq]
  let pack := D.powerset ×ˢ (Finset.range (n+1) ×ˢ Finset.range (k+1))
  let mono := fun p : Finset (Fin n) × (ℕ × ℕ) =>
    Finsupp.single Var.x p.2.1 + Finsupp.single Var.w p.2.2 + yMono p.1
  have hc (e : Var n →₀ ℕ) : MvPolynomial.coeff e P = ((A.filter (fun S => exp S = e)).card : ℚ) := by
    simp only [P,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    simp [Finset.sum_boole,eq_comm]
  have hs : P.support ⊆ pack.image mono := by
    intro e he
    have hn := MvPolynomial.mem_support_iff.mp he
    rw [hc] at hn
    obtain ⟨S,hS⟩ := Finset.card_pos.mp (by exact_mod_cast (show 0 < (((A.filter (fun S => exp S=e)).card):ℚ) by positivity))
    obtain ⟨hA,heq⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_image.mpr ⟨(S ∩ D,(S \ D).card,mu G W S),?_,heq⟩
    apply Finset.mem_product.mpr;refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,Finset.mem_product.mpr ⟨?_,?_⟩⟩
    · apply Finset.mem_range.mpr
      have h : (S \ D).card ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      exact Nat.lt_succ_of_le h
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hk S hA))
  constructor
  · have h := (Finset.card_le_card hs).trans Finset.card_image_le
    simpa [pack,mul_assoc] using h
  constructor
  · intro e
    refine ⟨_,?_,hc e⟩
    have hb := (Finset.card_le_card (Finset.filter_subset (fun S => exp S=e) A)).trans (Finset.card_le_univ _)
    simpa using hb


  · intro e he
    obtain ⟨⟨F,i,j⟩,h,hh⟩ := Finset.mem_image.mp (hs he)
    have ij := (Finset.mem_product.mp (Finset.mem_product.mp h).2)
    have hi := Finset.mem_range.mp ij.1
    have hj := Finset.mem_range.mp ij.2
    change i < n+1 at hi
    change j < k+1 at hj
    subst e
    have val (v : Fin n) : yMono F (Var.y v) = if v ∈ F then 1 else 0 := by
      simp [yMono,Finsupp.finsetSum_apply,Finsupp.single_apply,eq_comm]
    simp [mono,yMono,Finsupp.single_apply,eq_comm]
    exact ⟨by omega, by omega, fun v => by split <;> omega⟩

private theorem filterValue {α : Type} [DecidableEq α] (l : List (α × ℚ)) (x : α × ℚ)
    (distinct : (l.map Prod.fst).Nodup) (member : x ∈ l) :
    ((l.filter (fun p => decide (p.1 = x.1))).map Prod.snd).sum = x.2 := by
  induction l with
  | nil => simp at member
  | cons a l ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with rfl | tail
    · have none : l.filter (fun p => decide (p.1 = x.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro p hp
        have ne : p.1 ≠ x.1 := fun e => fresh (List.mem_map.mpr ⟨p,hp,e⟩)
        simp [ne]
      simp [none]
    · have ne : a.1 ≠ x.1 := fun e => fresh (List.mem_map.mpr ⟨x,tail,e.symm⟩)
      simpa [ne] using ih nd tail

/-- Witness the sparse representation of every finite polynomial, including
the zero polynomial. The representation fixes one order of its nonzero monomials. -/
theorem polynomialSparse {n : ℕ} (P : MvPolynomial (Var n) ℚ) :
    ∃ L, IsSparseRep L (fun e => MvPolynomial.coeff e P) := by
  classical
  let L := P.support.toList.map (fun e => (e,MvPolynomial.coeff e P))
  have key : (L.map Prod.fst).Nodup := by simpa [L,List.map_map,Function.comp_def] using P.support.nodup_toList
  have info (p) (h : p ∈ L) : p.1 ∈ P.support ∧ p.2 = MvPolynomial.coeff p.1 P := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
    exact ⟨Finset.mem_toList.mp he,rfl⟩
  refine ⟨L,key,fun p h => (info p h).2 ▸ MvPolynomial.mem_support_iff.mp (info p h).1,?_⟩
  intro e
  by_cases h : e ∈ P.support
  · have mem : (e,MvPolynomial.coeff e P) ∈ L :=
      List.mem_map.mpr ⟨e,Finset.mem_toList.mpr h,rfl⟩
    exact (filterValue L _ key mem).symm
  · have clear : L.filter (fun p => decide (p.1 = e)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro p hp
      have ne : p.1 ≠ e := fun eq => h (eq ▸ (info p hp).1)
      simp [ne]
    have zero : MvPolynomial.coeff e P = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    simp [clear,zero]

private theorem naturalWidth (m : ℕ) : (encodeNat m).length = 2*m.size+1 := by
  simp [encodeNat, Nat.size_eq_bits_len, two_mul]; omega

private theorem wordCost {n k : ℕ} (e : Var n →₀ ℕ) (j : ℕ) (hj : j ≤ 2^n)
    (hx : e Var.x ≤ n) (hp : e Var.x' = 0) (hw : e Var.w ≤ k) (hy : ∀ v, e (Var.y v) ≤ 1) :
    (encodeExp e ++ encodeRat (j:ℚ)).length ≤ 8*(n+k+1)+8 := by
  have width (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self
  have jl : j.size ≤ n+1 := Nat.size_le.mpr (by rw [pow_succ]; have := Nat.two_pow_pos n; omega)
  have J : (encodeRat (j:ℚ)).length ≤ 2*n+7 := by
    simp only [encodeRat, encodeInt, List.length_append, List.length_cons, Rat.num_natCast,
      Rat.den_natCast, Int.natAbs_natCast, naturalWidth]
    change 2*j.size + 1 + 1 + (2*1+1) ≤ _
    omega
  have flat (l : List (Fin n)) :
      (l.flatMap (fun v => encodeNat (e (Var.y v)))).length ≤ l.length*3 := by
    induction l with
    | nil => simp
    | cons v l ih =>
      simp only [List.flatMap_cons, List.length_append, naturalWidth,List.length_cons,Nat.succ_mul]
      have h := (width _).trans (hy v)
      omega
  have f := flat (List.finRange n)
  rw [List.length_finRange] at f
  simp only [encodeExp, List.length_append, naturalWidth, hp]
  have x := (width _).trans hx
  have w := (width _).trans hw
  have z : (0:ℕ).size = 0 := rfl
  omega

/-- Actual binary length of a list of nonzero coefficients, for both the full
and large-bag DP polynomial. The term order is arbitrary. -/
theorem sparseBoxes {n : ℕ} (G : SimpleGraph (Fin n)) (W B D : Finset (Fin n)) (k : ℕ)
    (P : MvPolynomial (Var n) ℚ)
    (which : P = omega D (Zfull G W k) ∨ P = omega D (Zle G W B k))
    (L : List ((Var n →₀ ℕ) × ℚ))
    (valid : IsSparseRep L (fun e => MvPolynomial.coeff e P)) :
    (encodeTerms L).length ≤ 1+2^D.card*(n+1)*(k+1)*(8*(n+k+1)+10) := by
  classical
  have props : P.support.card ≤ 2^D.card*(n+1)*(k+1) ∧
      (∀ e, ∃ j : ℕ, j ≤ 2^n ∧ MvPolynomial.coeff e P = (j:ℚ)) ∧
      ∀ e ∈ P.support, e Var.x ≤ n ∧ e Var.x' = 0 ∧ e Var.w ≤ k ∧ ∀ v, e (Var.y v) ≤ 1 := by
    rcases which with rfl | rfl
    · exact renamed_cut_support G W D k _ (fun _ h => (Finset.mem_filter.mp h).2)
    · exact renamed_cut_support G W D k _ (fun _ h => (Finset.mem_filter.mp h).2.1)
  obtain ⟨card,coeff,shape⟩ := props
  have eval (p) (h : p ∈ L) : MvPolynomial.coeff p.1 P = p.2 :=
    (valid.2.2 p.1).trans (filterValue L p valid.1 h)
  have supp (p) (h : p ∈ L) : p.1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr ((eval p h) ▸ valid.2.1 p h)
  have sub : (L.map Prod.fst).toFinset ⊆ P.support := by
    intro e h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact supp p hp
  have length := (Finset.card_le_card sub).trans card
  rw [List.toFinset_card_of_nodup valid.1,List.length_map] at length
  have each (p) (h : p ∈ L) : (encodeExp p.1 ++ encodeRat p.2).length ≤ 8*(n+k+1)+8 := by
    obtain ⟨j,hj,hv⟩ := coeff p.1
    rw [← eval p h,hv]
    obtain ⟨hx,hp,hw,hy⟩ := shape _ (supp p h)
    exact wordCost p.1 j hj hx hp hw hy
  have flat (l : List ((Var n →₀ ℕ) × ℚ)) (sub : ∀ p∈l, p ∈ L) :
      (l.flatMap (fun p => encodeExp p.1 ++ encodeRat p.2)).length ≤ l.length*(8*(n+k+1)+8) := by
    induction l with
    | nil => simp
    | cons p l ih =>
      rw [List.flatMap_cons,List.length_append,List.length_cons, Nat.succ_mul]
      have h₁ := each p (sub p (by simp))
      have h₂ := ih (fun p hp => sub p (by simp [hp]))
      omega
  simp only [encodeTerms, List.length_append,naturalWidth]
  have f := flat L (fun _ h => h)
  have w : L.length.size ≤ L.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have major := Nat.mul_le_mul_right (8*(n+k+1)+10) length
  have split : L.length*(8*(n+k+1)+10) = L.length*(8*(n+k+1)+8) + 2*L.length := by ring
  omega

theorem sparseCost {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n) (s : Fin T.N)
    (L : List ((Var n →₀ ℕ) × ℚ))
    (valid : IsSparseRep L (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    (encodeTerms L).length ≤ 1+2^(T.adhesion s).card*(n+1)*(k+1)*(8*(n+k+1)+10) :=
  sparseBoxes G (T.cone s) (T.bag s) (T.adhesion s) k _ (Or.inl rfl) L valid

end SingleExpBisect.Machine

set_option autoImplicit false
open scoped Classical
namespace SingleExpBisect.Machine
open MinBisectFPT SingleExpBisect.Main ExponomialAssortment.FPTAS

private theorem encWidth (i : ℕ) : (encodeNat i).length ≤ 2*i+1 := by
  have w : i.size ≤ i := Nat.size_le.mpr Nat.lt_two_pow_self
  simpa [encodeNat,← Nat.size_eq_bits_len,two_mul,add_comm,add_left_comm,add_assoc] using
    Nat.add_le_add (Nat.add_le_add w w) (le_refl 1)

private theorem unitBound (n k d : ℕ) (hd : d ≤ 2*k) :
    1+2^d*(n+1)*(k+1)*(8*(n+k+1)+10) ≤ 19*2^(4*k)*(n+1)^2 := by
  have kbound : k+1 ≤ 2^k := Nat.lt_two_pow_self
  have a : 2^d*(n+1)*(k+1) ≤ 2^(2*k)*(n+1)*2^k :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hd)) kbound
  have b : 8*(n+k+1)+10 ≤ 18*(n+1)*2^k := by
    apply le_trans _ (Nat.mul_le_mul_left (18*(n+1)) kbound)
    ring_nf; omega
  have c := Nat.mul_le_mul a b
  have d' : 2^(2*k)*(n+1)*2^k * (18*(n+1)*2^k) =
      18*2^(4*k)*(n+1)^2 := by
    rw [show 4*k = 2*k+k+k by omega, pow_add, pow_add]; ring
  rw [d'] at c
  have pos : 0 < 2^(4*k)*(n+1)^2 := by positivity
  apply le_trans (Nat.add_le_add_left c 1)
  rw [Nat.mul_assoc 18,Nat.mul_assoc 19]
  omega

/-- Total bit length of all sparse child polynomials, uniformly over their term
orders and every legal decomposition. Every coefficient and exponent is counted. -/
theorem childrenLength {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n)
    (t : Fin T.N) (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ)) (valid : IsSec3Decomp G T k)
    (children : ∀ s, T.parent s = some t →
      IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    (childInput T t Lc).length ≤ 22*2^(4*k)*(n+1)^3 := by
  classical
  let ids := (List.finRange T.N).filter (fun s => decide (T.parent s = some t))
  have num := valid.2.2.2.1
  have atMost : T.N ≤ n+1 := by omega
  have diam : (n+1) ≤ 2^(4*k)*(n+1)^2 := by
    have a : 1 ≤ 2^(4*k) := Nat.succ_le_of_lt (by positivity)
    have h := Nat.mul_le_mul_right ((n+1)^2) a
    simp only [Nat.one_mul] at h
    apply le_trans _ h
    ring_nf; omega
  have enc (s : Fin T.N) (h : s ∈ ids) :
      (encodeNat s.val ++ encodeTerms (Lc s)).length ≤ 22*2^(4*k)*(n+1)^2 := by
    have hp : T.parent s = some t := of_decide_eq_true (List.mem_filter.mp h).2
    have ts := (sparseCost G k T s (Lc s) (children s hp)).trans (unitBound n k _ (valid.2.1 s))
    have vs := encWidth s.val
    have hlt := s.isLt
    rw [List.length_append]
    calc
      _ ≤ 2*(n+1)+1 + 19*2^(4*k)*(n+1)^2 := by omega
      _ ≤ 22*2^(4*k)*(n+1)^2 := by
        rw [show 19*2^(4*k)*(n+1)^2=19*(2^(4*k)*(n+1)^2) by ring,
          show 22*2^(4*k)*(n+1)^2=22*(2^(4*k)*(n+1)^2) by ring]
        omega
  have flat (l : List (Fin T.N)) (inside : ∀ s ∈ l, s ∈ ids) :
      (l.flatMap (fun s => encodeNat s.val ++ encodeTerms (Lc s))).length ≤
        l.length * (22*2^(4*k)*(n+1)^2) := by
    induction l with
    | nil => simp
    | cons s l ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      have a := enc s (inside s (by simp))
      have b := ih (fun x hx => inside x (by simp [hx]))
      omega
  have len : ids.length ≤ n+1 :=
    (List.length_filter_le _ _).trans (List.length_finRange.le.trans atMost)
  exact (flat ids (fun _ h => h)).trans
    ((Nat.mul_le_mul_right _ len).trans_eq (by ring))

/-- All input bits of Lemma 3.4 (and the shorter inputs of 3.5 and 3.6)
fit within the official single-exponential time budget. -/
theorem fullInputBudget {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n)
    (t : Fin T.N) (S : Finset (Fin n)) (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ))
    (valid : IsSec3Decomp G T k)
    (children : ∀ s, T.parent s = some t →
      IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    (nodeInput G k T t ++ encodeSet S ++ childInput T t Lc).length+1 ≤ stepBound 64 k n ∧
    (nodeInput G k T t ++ childInput T t Lc).length+1 ≤ stepBound 64 k n := by
  have node := nodeBudget G k T valid t
  have ch := childrenLength G k T t Lc valid children
  have se := setLength S
  let z := 2^(64*k)*(n+1)^64
  have comparison (i j : ℕ) (hi : i ≤ 64*k) (hj : j ≤ 64) :
      2^i*(n+1)^j ≤ z :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hi) (Nat.pow_le_pow_right (by omega) hj)
  have a := Nat.mul_le_mul_left 32 (comparison (32*k) 32 (by omega) (by decide))
  have b := Nat.mul_le_mul_left 22 (comparison (4*k) 3 (by omega) (by decide))
  have c := Nat.mul_le_mul_left 2 (comparison 0 2 (Nat.zero_le _) (by decide))
  have h : (n+1)*(2*n+1) ≤ 2*(n+1)^2 := by ring_nf; omega
  simp only [pow_zero,Nat.one_mul] at c
  simp only [stepBound,Nat.mul_assoc] at node ⊢
  rw [Nat.mul_assoc] at ch
  change _ ≤ 64*z ∧ _ ≤ 64*z
  simp only [List.length_append]
  omega

private theorem outputBudget (n k b : ℕ) (h : b ≤ 19*2^(4*k)*(n+1)^2) :
    b+1 ≤ stepBound 64 k n := by
  have lift : 2^(4*k)*(n+1)^2 ≤ 2^(64*k)*(n+1)^64 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.pow_le_pow_right (by omega) (by decide))
  have pos : 0 < 2^(64*k)*(n+1)^64 :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.succ_pos _))
  rw [Nat.mul_assoc] at h
  simp only [stepBound,Nat.mul_assoc]
  omega

/-- For the inputs of 3.4--3.6 and the output polynomials of 3.5 and 3.6,
all of the actual bit strings fit one common registered budget. In particular
the bound is independent of the order in every sparse term list. -/
theorem dataVolume {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n)
    (t : Fin T.N) (S : Finset (Fin n)) (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ))
    (valid : IsSec3Decomp G T k)
    (children : ∀ s, T.parent s = some t →
      IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    (nodeInput G k T t ++ encodeSet S ++ childInput T t Lc).length+1 ≤ stepBound 64 k n ∧
    (nodeInput G k T t ++ childInput T t Lc).length+1 ≤ stepBound 64 k n ∧
    ∀ P : MvPolynomial (Var n) ℚ,
      (P = Zomega G T k t ∨ P = omega (T.adhesion t) (Zle G (T.cone t) (T.bag t) k)) →
      (∃ L, IsSparseRep L (fun e => MvPolynomial.coeff e P)) ∧
      ∀ L : List ((Var n →₀ ℕ) × ℚ), IsSparseRep L (fun e => MvPolynomial.coeff e P) →
        (encodeTerms L).length+1 ≤ stepBound 64 k n := by
  obtain ⟨withSet,without⟩ := fullInputBudget G k T t S Lc valid children
  refine ⟨withSet,without,?_⟩
  intro P shape
  refine ⟨polynomialSparse P,?_⟩
  intro L correct
  have out := (sparseBoxes G (T.cone t) (T.bag t) (T.adhesion t) k P shape L correct).trans
    (unitBound n k _ (valid.2.1 t))
  exact outputBudget n k _ out

end SingleExpBisect.Machine

open scoped Classical
open SingleExpBisect.Main MinBisectFPT ExponomialAssortment.FPTAS
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n)
    (t : Fin T.N) (S : Finset (Fin n)) (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ))
    (valid : IsSec3Decomp G T k)
    (children : ∀ s, T.parent s = some t →
      IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) :
    (nodeInput G k T t ++ encodeSet S ++ childInput T t Lc).length+1 ≤ stepBound 64 k n ∧
    (nodeInput G k T t ++ childInput T t Lc).length+1 ≤ stepBound 64 k n ∧
    ∀ P : MvPolynomial (Var n) ℚ,
      (P = Zomega G T k t ∨ P = omega (T.adhesion t) (Zle G (T.cone t) (T.bag t) k)) →
      (∃ L, IsSparseRep L (fun e => MvPolynomial.coeff e P)) ∧
      ∀ L : List ((Var n →₀ ℕ) × ℚ), IsSparseRep L (fun e => MvPolynomial.coeff e P) →
        (encodeTerms L).length+1 ≤ stepBound 64 k n := by
  exact SingleExpBisect.Machine.dataVolume G k T t S Lc valid children

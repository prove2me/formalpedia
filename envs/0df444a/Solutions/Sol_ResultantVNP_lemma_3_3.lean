-- Prove2me | solution 1 for ResultantVNP.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T15:49:01.3484+00:00
-- url     : https://prove2.me/submissions/feabe04d-35cf-4357-9958-775731294321

import Theorems.Thm_ResultantVNP_grid_permanent_identity
import Theorems.Thm_ResultantVNP_grid_table_polytime
import Definitions.Def_ResultantVNP_gridTensor
import Definitions.Def_ResultantVNP_SupportedOnGrid

open ResultantVNP Finset MvPolynomial
open scoped Classical

namespace GridConstruction

theorem side_form (n : ℕ) : ∃ r,1 ≤ r ∧ gridSide n = 3 ^ r + 1 :=
  ⟨Nat.find (gridSide_exists n),(Nat.find_spec (gridSide_exists n)).1,rfl⟩

theorem side_gt (n : ℕ) : n < gridSide n := (Nat.find_spec (gridSide_exists n)).2

theorem side_ge_four (n : ℕ) : 4 ≤ gridSide n := by
  obtain ⟨r,hr,he⟩ := side_form n
  have h := Nat.pow_le_pow_right (by omega : 1 ≤ 3) hr
  rw [he]
  norm_num at h
  omega

theorem side_linear (n : ℕ) (hn : 1 ≤ n) : gridSide n ≤ 4 * n := by
  let r := Nat.find (gridSide_exists n)
  have hr : 1 ≤ r := (Nat.find_spec (gridSide_exists n)).1
  change 3 ^ r + 1 ≤ 4 * n
  by_cases he : r = 1
  · rw [he]
    norm_num
    omega
  · have hprev : ¬ (1 ≤ r-1 ∧ n < 3 ^ (r-1) + 1) :=
      Nat.find_min (gridSide_exists n) (by omega : r-1 < r)
    have hpow : 3 ^ (r-1) ≤ n := by omega
    have hs : r = r-1+1 := by omega
    rw [hs,pow_succ]
    omega

theorem state_card : Fintype.card GridState = 5 := by decide

theorem class_card (m : ℕ) [NeZero m] (p : ZMod m × ZMod m) :
    Fintype.card {α : GridIdx m // α.1 = p} = 5 := by
  let e : {α : GridIdx m // α.1 = p} ≃ GridState :=
    { toFun := fun a => a.val.2
      invFun := fun a => ⟨(p,a),rfl⟩
      left_inv := by intro a; apply Subtype.ext; exact Prod.ext a.property.symm rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans state_card

theorem encoding_supported (n m : ℕ) [NeZero m] :
    SupportedOnGrid (fun α : GridIdx m => α.1) (gridEncoding n m) := by
  classical
  intro T hT
  unfold gridEncoding at hT
  obtain ⟨p,_,hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  obtain ⟨a,_,ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  obtain ⟨b,_,hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨c,_,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  by_cases ht : T = (p,a) ::ₛ (gridRight p,b) ::ₛ (gridDown p,c) ::ₛ Sym.nil ∧ gridTest m p a b c
  · exact ⟨p,(p,a),(gridRight p,b),(gridDown p,c),rfl,rfl,rfl,ht.1⟩
  · simp [ht] at hc

def triangle {m : ℕ} (p : ZMod m × ZMod m) : Sym (ZMod m × ZMod m) 3 :=
  p ::ₛ gridRight p ::ₛ gridDown p ::ₛ Sym.nil

lemma three_unit (r : ℕ) (hr : 1 ≤ r) : IsUnit (3 : ZMod (3^r+1)) := by
  apply (ZMod.isUnit_iff_coprime 3 (3^r+1)).mpr
  have h : Nat.Coprime (3^r) (3^r+1) := by simp
  exact h.of_dvd_left (dvd_pow_self 3 (by omega))

lemma triangle_injective (r : ℕ) (hr : 1 ≤ r) :
    Function.Injective (triangle (m := 3^r+1)) := by
  intro p q h
  have h1 := congrArg (fun T : Sym (ZMod (3^r+1) × ZMod (3^r+1)) 3 =>
    ((T : Multiset (ZMod (3^r+1) × ZMod (3^r+1))).map (fun p => p.1)).sum) h
  have h2 := congrArg (fun T : Sym (ZMod (3^r+1) × ZMod (3^r+1)) 3 =>
    ((T : Multiset (ZMod (3^r+1) × ZMod (3^r+1))).map (fun p => p.2)).sum) h
  have hfst : (3 : ZMod (3^r+1)) * p.1 = 3 * q.1 := by
    simp only [triangle,gridRight,gridDown,Sym.coe_cons,Sym.coe_nil,
      Multiset.map_cons,Multiset.map_zero,Multiset.sum_cons,Multiset.sum_zero] at h1
    linear_combination h1
  have hsnd : (3 : ZMod (3^r+1)) * p.2 = 3 * q.2 := by
    simp only [triangle,gridRight,gridDown,Sym.coe_cons,Sym.coe_nil,
      Multiset.map_cons,Multiset.map_zero,Multiset.sum_cons,Multiset.sum_zero] at h2
    linear_combination h2
  exact Prod.ext ((three_unit r hr).mul_left_cancel hfst) ((three_unit r hr).mul_left_cancel hsnd)


lemma triangle_injective_side (n : ℕ) : Function.Injective (triangle (m := gridSide n)) :=
  triangle_injective (Nat.find (gridSide_exists n)) (Nat.find_spec (gridSide_exists n)).1

def entryTriangle {m : ℕ} (p : ZMod m × ZMod m) (a b c : GridState) : Sym (GridIdx m) 3 :=
  (p,a) ::ₛ (gridRight p,b) ::ₛ (gridDown p,c) ::ₛ Sym.nil

lemma entryTriangle_classes {m : ℕ} (p : ZMod m × ZMod m) (a b c : GridState) :
    Sym.map Prod.fst (entryTriangle p a b c) = triangle p := by
  simp only [entryTriangle,triangle,Sym.map_cons]
  rfl

lemma positions_distinct {m : ℕ} (hm : 3 ≤ m) (p : ZMod m × ZMod m) :
    p ≠ gridRight p ∧ p ≠ gridDown p ∧ gridRight p ≠ gridDown p := by
  letI : Fact (1 < m) := ⟨by omega⟩
  constructor
  · intro h
    have h' := congrArg Prod.fst h
    simpa [gridRight] using h'
  · constructor
    · intro h
      have h' := congrArg Prod.snd h
      simpa [gridDown] using h'
    · intro h
      have h' := congrArg Prod.fst h
      simpa [gridRight,gridDown] using h'

lemma entryTriangle_states {m : ℕ} (hm : 3 ≤ m) (p : ZMod m × ZMod m)
    (a b c a' b' c' : GridState) (h : entryTriangle p a b c = entryTriangle p a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨hpr,hpd,hrd⟩ := positions_distinct hm p
  have ha : (p,a) ∈ entryTriangle p a' b' c' := by rw [← h]; simp [entryTriangle]
  have hb : (gridRight p,b) ∈ entryTriangle p a' b' c' := by rw [← h]; simp [entryTriangle]
  have hc : (gridDown p,c) ∈ entryTriangle p a' b' c' := by rw [← h]; simp [entryTriangle]
  simp only [entryTriangle,Sym.mem_cons,Sym.notMem_nil,or_false,Prod.mk.injEq] at ha hb hc
  exact ⟨by simpa [hpr,hpd] using ha,
    by simpa [hpr.symm,hrd] using hb,
    by simpa [hpd.symm,hrd.symm] using hc⟩

theorem entryTriangle_injective (n : ℕ) :
    Function.Injective (fun u : (ZMod (gridSide n) × ZMod (gridSide n)) × GridState × GridState × GridState =>
      entryTriangle u.1 u.2.1 u.2.2.1 u.2.2.2) := by
  intro u v h
  obtain ⟨p,a,b,c⟩ := u
  obtain ⟨p',a',b',c'⟩ := v
  have hcls := congrArg (Sym.map (Prod.fst : GridIdx (gridSide n) → _)) h
  simp only [entryTriangle_classes] at hcls
  have hp := triangle_injective_side n hcls
  subst p'
  have hs := entryTriangle_states (by have := side_ge_four n; omega) p a b c a' b' c' h
  rcases hs with ⟨rfl,rfl,rfl⟩
  rfl

theorem encoding_entry (n : ℕ) (p : ZMod (gridSide n) × ZMod (gridSide n)) (a b c : GridState) :
    gridTensor n (entryTriangle p a b c) =
      if gridTest (gridSide n) p a b c then
        (if a.1.1 = 1 then paddedEntry n (gridSide n) p else 1) else 0 := by
  classical
  unfold gridTensor gridEncoding
  have heq (p' : ZMod (gridSide n) × ZMod (gridSide n)) (a' b' c' : GridState) :
      entryTriangle p a b c = entryTriangle p' a' b' c' ↔
        p = p' ∧ a = a' ∧ b = b' ∧ c = c' := by
    simpa only [Prod.mk.injEq] using (entryTriangle_injective n).eq_iff
      (a := (p,a,b,c)) (b := (p',a',b',c'))
  change (∑ p',∑ a',∑ b',∑ c',if entryTriangle p a b c = entryTriangle p' a' b' c' ∧
    gridTest (gridSide n) p' a' b' c' then
      (if a'.1.1 = 1 then paddedEntry n (gridSide n) p' else 1) else 0) = _
  simp_rw [heq]
  simp [ite_and,Finset.sum_ite_irrel]

lemma paddedEntry_cases (n m : ℕ) (p : ZMod m × ZMod m) :
    paddedEntry n m p = 0 ∨ paddedEntry n m p = 1 ∨ ∃ ij,paddedEntry n m p = X ij := by
  unfold paddedEntry
  split_ifs
  · exact Or.inr (Or.inr ⟨_,rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem tensor_entries (n : ℕ) (T : Sym (GridIdx (gridSide n)) 3) :
    gridTensor n T = 0 ∨ gridTensor n T = 1 ∨ ∃ ij,gridTensor n T = X ij := by
  by_cases hz : gridTensor n T = 0
  · exact Or.inl hz
  obtain ⟨p,a,b,c,ha,hb,hc,hT⟩ := encoding_supported n (gridSide n) T hz
  have ha' : a = (p,a.2) := Prod.ext ha rfl
  have hb' : b = (gridRight p,b.2) := Prod.ext hb rfl
  have hc' : c = (gridDown p,c.2) := Prod.ext hc rfl
  rw [ha',hb',hc'] at hT
  change T = entryTriangle p a.2 b.2 c.2 at hT
  rw [hT,encoding_entry]
  split_ifs
  · exact paddedEntry_cases n (gridSide n) p
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem assignment_zero_one (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℤ)
    (hZ : ∀ i j,Z i j = 0 ∨ Z i j = 1)
    (ν : ∀ p,{α : GridIdx (gridSide n) // α.1 = p}) :
    eval (fun ij => Z ij.1 ij.2) (∏ p,gridTensor n (assignTriple (fun α => α.1) ν p)) = 0 ∨
      eval (fun ij => Z ij.1 ij.2) (∏ p,gridTensor n (assignTriple (fun α => α.1) ν p)) = 1 := by
  classical
  rw [map_prod]
  have hentry (p : ZMod (gridSide n) × ZMod (gridSide n)) :
      eval (fun ij => Z ij.1 ij.2) (gridTensor n (assignTriple (fun α => α.1) ν p)) = 0 ∨
        eval (fun ij => Z ij.1 ij.2) (gridTensor n (assignTriple (fun α => α.1) ν p)) = 1 := by
    rcases tensor_entries n (assignTriple (fun α => α.1) ν p) with hz | ho | ⟨ij,hij⟩
    · left; rw [hz,map_zero]
    · right; rw [ho,map_one]
    · rw [hij,eval_X]; exact hZ ij.1 ij.2
  by_cases hz : ∃ p,eval (fun ij => Z ij.1 ij.2) (gridTensor n (assignTriple (fun α => α.1) ν p)) = 0
  · obtain ⟨p,hp⟩ := hz
    exact Or.inl (Finset.prod_eq_zero (Finset.mem_univ p) hp)
  · right
    apply Finset.prod_eq_one
    intro p _
    exact (hentry p).resolve_left (fun hp => hz ⟨p,hp⟩)

lemma count_ones_eq_sum {α : Type} [Fintype α] (f : α → ℤ) (hf : ∀ a,f a = 0 ∨ f a = 1) :
    (Fintype.card {a // f a = 1} : ℤ) = ∑ a,f a := by
  classical
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Nat.cast_one,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  rcases hf a with h | h <;> simp [h]

lemma permanent_count (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℤ)
    (hZ : ∀ i j,Z i j = 0 ∨ Z i j = 1) :
    Z.permanent = (Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i,Z i (σ i) = 1} : ℤ) := by
  classical
  have hprod (σ : Equiv.Perm (Fin n)) :
      (∏ i,Z i (σ i)) = if ∀ i,Z i (σ i) = 1 then 1 else 0 := by
    split_ifs with h
    · exact Finset.prod_eq_one (fun i _ => h i)
    · push_neg at h
      obtain ⟨i,hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) ((hZ i (σ i)).resolve_right hi)
  rw [← Matrix.permanent_transpose Z,Matrix.permanent]
  simp only [Matrix.transpose_apply,hprod]
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Nat.cast_one,Finset.sum_filter]

theorem count_preservation_of_identity (n : ℕ)
    (hid : gridSum (fun α : GridIdx (gridSide n) => α.1) (gridTensor n) =
      (Matrix.of fun i j : Fin n => (X (i,j) : MvPolynomial (Fin n × Fin n) ℤ)).permanent)
    (Z : Matrix (Fin n) (Fin n) ℤ) (hZ : ∀ i j,Z i j = 0 ∨ Z i j = 1) :
    Fintype.card {ν : (∀ p,{α : GridIdx (gridSide n) // α.1 = p}) //
      eval (fun ij => Z ij.1 ij.2) (∏ p,gridTensor n (assignTriple (fun α => α.1) ν p)) = 1} =
      Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i,Z i (σ i) = 1} := by
  classical
  have heval := congrArg (eval (fun ij => Z ij.1 ij.2)) hid
  rw [gridSum,map_sum] at heval
  have hright : eval (fun ij => Z ij.1 ij.2)
      (Matrix.of fun i j : Fin n => (X (i,j) : MvPolynomial (Fin n × Fin n) ℤ)).permanent = Z.permanent := by
    simp [Matrix.permanent]
  rw [hright,permanent_count n Z hZ] at heval
  exact_mod_cast (count_ones_eq_sum _ (assignment_zero_one n Z hZ)).trans heval

end GridConstruction


theorem solution :
    (∃ C : ℕ, ∀ n, 1 ≤ n → gridSide n ≤ C * n) ∧
    Nonempty (Turing.TM2ComputableInPolyTime Computability.unaryEncodeNat id gridTableCode) ∧
    ∀ n, 1 ≤ n →
      (∃ r, 1 ≤ r ∧ gridSide n = 3 ^ r + 1) ∧ n < gridSide n ∧
      SupportedOnGrid (fun α : GridIdx (gridSide n) => α.1) (gridTensor n) ∧
      (∀ p : ZMod (gridSide n) × ZMod (gridSide n),
        Fintype.card {α : GridIdx (gridSide n) // α.1 = p} = 5) ∧
      (∀ T, gridTensor n T = 0 ∨ gridTensor n T = 1 ∨ ∃ ij, gridTensor n T = MvPolynomial.X ij) ∧
      gridSum (fun α : GridIdx (gridSide n) => α.1) (gridTensor n) =
        (Matrix.of fun i j : Fin n => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℤ)).permanent ∧
      ∀ Z : Matrix (Fin n) (Fin n) ℤ, (∀ i j, Z i j = 0 ∨ Z i j = 1) →
        (∀ ν : (∀ p, {α : GridIdx (gridSide n) // α.1 = p}),
          MvPolynomial.eval (fun ij => Z ij.1 ij.2)
              (∏ p, gridTensor n (assignTriple (fun α => α.1) ν p)) = 0 ∨
            MvPolynomial.eval (fun ij => Z ij.1 ij.2)
              (∏ p, gridTensor n (assignTriple (fun α => α.1) ν p)) = 1) ∧
        Fintype.card {ν : (∀ p, {α : GridIdx (gridSide n) // α.1 = p}) //
            MvPolynomial.eval (fun ij => Z ij.1 ij.2)
              (∏ p, gridTensor n (assignTriple (fun α => α.1) ν p)) = 1} =
          Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i, Z i (σ i) = 1} := by
  refine ⟨⟨4,GridConstruction.side_linear⟩,ResultantVNP.grid_table_polytime,?_⟩
  intro n hn
  refine ⟨GridConstruction.side_form n,GridConstruction.side_gt n,
    GridConstruction.encoding_supported n (gridSide n),GridConstruction.class_card (gridSide n),
    GridConstruction.tensor_entries n,ResultantVNP.grid_permanent_identity n,?_⟩
  intro Z hZ
  exact ⟨GridConstruction.assignment_zero_one n Z hZ,
    GridConstruction.count_preservation_of_identity n (ResultantVNP.grid_permanent_identity n) Z hZ⟩

#print axioms solution

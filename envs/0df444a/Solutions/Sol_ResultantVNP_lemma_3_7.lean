-- Prove2me | solution 1 for ResultantVNP.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T13:06:51.555697+00:00
-- url     : https://prove2.me/submissions/49c95e80-092e-42e5-ad88-44fa721c3761

import Theorems.Thm_ResultantVNP_lemma_3_6
import Definitions.Def_ResultantVNP_SupportedOnGrid
import Theorems.Thm_ResultantVNP_lemma_3_4
import Theorems.Thm_ResultantVNP_theorem_3_5

namespace CharacteristicHomogeneity

open MvPolynomial

private noncomputable def affine {σ : Type} (δ : σ → ℤ) (v : σ) :
    Polynomial (MvPolynomial σ ℤ) :=
  Polynomial.C (C (δ v)) + Polynomial.X * Polynomial.C (X v)

theorem coefficient_homogeneous {σ : Type} (δ : σ → ℤ) (p : MvPolynomial σ ℤ) :
    ∀ s, ((aeval (affine δ) p).coeff s).IsHomogeneous s := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro s
    have hc : aeval (affine δ) (C a) = (Polynomial.C (C a) : Polynomial (MvPolynomial σ ℤ)) := by
      simp
    rw [hc]
    cases s with
    | zero => simpa using isHomogeneous_C σ a
    | succ s =>
      rw [Polynomial.coeff_C]
      simp only [Nat.succ_ne_zero, ite_false]
      exact isHomogeneous_zero σ ℤ (s + 1)
  | add p q hp hq =>
    intro s
    rw [map_add, Polynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    rw [map_mul, aeval_X]
    change ((aeval (affine δ) p * (Polynomial.C (C (δ v)) +
      Polynomial.X * Polynomial.C (X v))).coeff s).IsHomogeneous s
    rw [mul_add, Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_C,
      Polynomial.coeff_mul_C]
    apply IsHomogeneous.add
    · simpa only [add_zero] using (hp s).mul (isHomogeneous_C σ (δ v))
    · cases s with
      | zero => simp only [Polynomial.coeff_mul_X_zero, zero_mul]; exact isHomogeneous_zero σ ℤ 0
      | succ s =>
        rw [Polynomial.coeff_mul_X]
        exact (hp s).mul (isHomogeneous_X ℤ v)

theorem charCoeff_homogeneous (𝓡 : ResultantVNP.ResultantSystem) (n s : ℕ) :
    (ResultantVNP.charCoeff 𝓡 n s).IsHomogeneous s := by
  classical
  let δ : Sym (Fin n) 3 → ℤ := fun T => if ∃ i, T = Sym.replicate 3 i then 1 else 0
  have h := coefficient_homogeneous δ (ResultantVNP.symTensorDet 𝓡 n) s
  convert h using 2
  unfold ResultantVNP.charCoeff
  apply congrArg (fun f : Sym (Fin n) 3 → Polynomial (MvPolynomial (Sym (Fin n) 3) ℤ) =>
    (aeval f (ResultantVNP.symTensorDet 𝓡 n)).coeff s)
  funext T
  simp [affine, δ, apply_ite]

end CharacteristicHomogeneity


set_option maxHeartbeats 200000
open Finset

namespace GridCounts

theorem counts_one (r : ℕ) (hr : 1 ≤ r)
    (b : ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1) → ℕ)
    (hb : ∀ i j, 3 ∣ b (i,j) + b (i-1,j) + b (i,j-1))
    (hs : ∑ p,b p = (3 ^ r + 1)^2) : ∀ p,b p = 1 := by
  classical
  have hc := ResultantVNP.lemma_3_6 r hr (fun p => (b p : ZMod 3)) (by
    intro i j
    have h := (CharP.cast_eq_zero_iff (ZMod 3) 3 _).mpr (hb i j)
    simpa only [Nat.cast_add] using h)
  let p₀ : ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1) := (0,0)
  have hpow : (3 : ZMod 3)^r = 0 := by
    rw [show (3 : ZMod 3) = 0 by decide,zero_pow (by omega)]
  have hcard : Fintype.card (ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1)) = (3 ^ r + 1)^2 := by
    simp [Fintype.card_prod,pow_two]
  have hsum := congrArg (Nat.cast : ℕ → ZMod 3) hs
  simp only [Nat.cast_sum,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hpow,zero_add,one_pow] at hsum
  have hconst : ∑ p,(b p : ZMod 3) = b p₀ := by
    simp_rw [hc _ p₀]
    rw [sum_const,card_univ,hcard,nsmul_eq_mul]
    simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hpow,zero_add,one_pow,one_mul]
  rw [hconst] at hsum
  have hpos (p) : 1 ≤ b p := by
    by_contra h
    have hb0 : b p = 0 := by omega
    have hbp := (hc p p₀).trans hsum
    simp [hb0] at hbp
  have heq : (∑ p,b p) = ∑ _p : ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1),1 := by
    simpa only [sum_const,card_univ,hcard,smul_eq_mul,mul_one] using hs
  have hpoint := (sum_eq_sum_iff_of_le (fun p _ => hpos p)).mp heq.symm
  intro p
  exact (hpoint p (mem_univ _)).symm

end GridCounts

namespace GridExtraction
open ResultantVNP

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

lemma assignment_classes {m : ℕ} {ι : Type} (cls : ι → ZMod m × ZMod m)
    (ν : ∀ p,{a // cls a = p}) (p : ZMod m × ZMod m) :
    Sym.map cls (assignTriple cls ν p) = triangle p := by
  simp [assignTriple,triangle,(ν p).2,(ν (gridRight p)).2,(ν (gridDown p)).2,
    show Sym.map cls (Sym.nil : Sym ι 0) = Sym.nil from Subsingleton.elim _ _]

lemma supported_classes {m : ℕ} {ι S : Type} [Zero S]
    (cls : ι → ZMod m × ZMod m) (A : Sym ι 3 → S) (hA : SupportedOnGrid cls A)
    (T : Sym ι 3) (hT : A T ≠ 0) : ∃ p,Sym.map cls T = triangle p := by
  obtain ⟨p,a,b,c,ha,hb,hc,rfl⟩ := hA T hT
  exact ⟨p,by simp [triangle,ha,hb,hc,
    show Sym.map cls (Sym.nil : Sym ι 0) = Sym.nil from Subsingleton.elim _ _]⟩

lemma count_map_sum {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (M : Multiset α) (b : β) :
    (M.map f).count b = ∑ a, if f a = b then M.count a else 0 := by
  classical
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons,Multiset.count_cons,ih]
    have hd (x y : ℕ) (P : Prop) [Decidable P] :
        (if P then x+y else 0) = (if P then x else 0) + (if P then y else 0) := by
      split_ifs <;> simp
    simp_rw [hd,Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp [eq_comm]
    · intro b _ hba; simp [hba]
    · simp

lemma count_triangle_bind {m : ℕ} [NeZero m]
    (B : Multiset (ZMod m × ZMod m)) (p : ZMod m × ZMod m) :
    (B.bind (fun q => (triangle q : Multiset (ZMod m × ZMod m)))).count p =
      B.count p + B.count (p.1-1,p.2) + B.count (p.1,p.2-1) := by
  classical
  have hiR : Function.Injective (gridRight (m := m)) := by
    intro a b h
    apply Prod.ext
    · exact add_right_cancel (congrArg (fun p : ZMod m × ZMod m => p.1) h)
    · have hh := congrArg (fun p : ZMod m × ZMod m => p.2) h
      exact hh
  have hiD : Function.Injective (gridDown (m := m)) := by
    intro a b h
    apply Prod.ext
    · have hh := congrArg (fun p : ZMod m × ZMod m => p.1) h
      exact hh
    · exact add_right_cancel (congrArg (fun p : ZMod m × ZMod m => p.2) h)
  have hR := Multiset.count_map_eq_count' gridRight B hiR (p.1-1,p.2)
  have hD := Multiset.count_map_eq_count' gridDown B hiD (p.1,p.2-1)
  simp only [gridRight,sub_add_cancel,Prod.mk.eta] at hR
  simp only [gridDown,sub_add_cancel,Prod.mk.eta] at hD
  simpa only [triangle,Sym.coe_cons,Sym.coe_nil,Multiset.bind_cons,Multiset.bind_zero,
    Multiset.map_id',add_zero,Multiset.count_add,hR,hD,add_assoc]

lemma class_counts {m : ℕ} [NeZero m] {ι : Type} [DecidableEq ι]
    (cls : ι → ZMod m × ZMod m) (M : Multiset (Sym ι 3))
    (f : Sym ι 3 → ZMod m × ZMod m)
    (hf : ∀ T ∈ M, Sym.map cls T = triangle (f T)) (p : ZMod m × ZMod m) :
    ((M.bind (fun T => (T : Multiset ι))).map cls).count p =
      (M.map f).count p + (M.map f).count (p.1-1,p.2) + (M.map f).count (p.1,p.2-1) := by
  rw [Multiset.map_bind]
  have heq : M.bind (fun T => (T : Multiset ι).map cls) =
      (M.map f).bind (fun p => (triangle p : Multiset (ZMod m × ZMod m))) := by
    rw [Multiset.bind_map]
    apply Multiset.bind_congr
    intro T hT
    exact congrArg (fun T : Sym (ZMod m × ZMod m) 3 => (T : Multiset (ZMod m × ZMod m))) (hf T hT)
  rw [heq,count_triangle_bind]

lemma count_vertices {ι : Type} [DecidableEq ι] (μ : Sym ι 3 →₀ ℕ) (i : ι) :
    (μ.toMultiset.bind (fun T => (T : Multiset ι))).count i =
      μ.sum (fun T k => k * Multiset.count i (T : Multiset ι)) := by
  classical
  induction μ using Finsupp.induction with
  | zero => simp
  | @single_add T k μ hT hk ih =>
    simp only [Finsupp.toMultiset_add,Finsupp.toMultiset_single,
      Multiset.add_bind,Multiset.count_add,ih]
    rw [Finsupp.sum_add_index]
    · rw [Multiset.bind,Multiset.map_nsmul,Multiset.map_singleton]
      simp only [Multiset.join,Multiset.sum_nsmul,Multiset.sum_singleton,Multiset.count_nsmul]
      simp
    · simp
    · intros; exact add_mul _ _ _

theorem assignment_of_monomial (r : ℕ) (hr : 1 ≤ r)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (cls : ι → ZMod (3^r+1) × ZMod (3^r+1)) (μ : Sym ι 3 →₀ ℕ)
    (hdegree : μ.sum (fun _ k => k) = (3^r+1)^2)
    (hdiv : ∀ i,3 ∣ μ.sum (fun T k => k * Multiset.count i (T : Multiset ι)))
    (hcard : (Finset.univ.filter (fun i =>
      0 < μ.sum (fun T k => k * Multiset.count i (T : Multiset ι)))).card ≤ (3^r+1)^2)
    (hgood : ∀ T ∈ μ.support, ∃ p,Sym.map cls T = triangle p) :
    ∃ ν : (∀ p,{a // cls a = p}), μ = assignMonomial cls ν := by
  classical
  let M := μ.toMultiset
  let V := M.bind (fun T => (T : Multiset ι))
  let f : Sym ι 3 → ZMod (3^r+1) × ZMod (3^r+1) := fun T =>
    if h : T ∈ μ.support then (hgood T h).choose else (0,0)
  have hf (T) (hT : T ∈ M) : Sym.map cls T = triangle (f T) := by
    have hT' : T ∈ μ.support := (Finsupp.mem_toMultiset μ T).mp hT
    simpa only [f,dif_pos hT'] using (hgood T hT').choose_spec
  have hclasses (p) : (V.map cls).count p =
      (M.map f).count p + (M.map f).count (p.1-1,p.2) + (M.map f).count (p.1,p.2-1) :=
    class_counts cls M f hf p
  have hcounts : ∀ p,(M.map f).count p = 1 := by
    apply GridCounts.counts_one r hr
    · intro i j
      rw [← hclasses, count_map_sum]
      apply Finset.dvd_sum
      intro a _
      split_ifs
      · exact (count_vertices μ a).symm ▸ hdiv a
      · exact dvd_zero _
    · rw [Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _),Multiset.card_map]
      exact (Finsupp.card_toMultiset μ).trans hdegree
  have hclass3 (p) : (V.map cls).count p = 3 := by rw [hclasses,hcounts,hcounts,hcounts]
  let I := V.toFinset
  let toClass : I → ZMod (3^r+1) × ZMod (3^r+1) := fun a => cls a.val
  have hsurj : Function.Surjective toClass := by
    intro p
    have hp : p ∈ V.map cls := Multiset.count_pos.mp (by rw [hclass3]; decide)
    obtain ⟨a,ha,hap⟩ := Multiset.mem_map.mp hp
    exact ⟨⟨a,Multiset.mem_toFinset.mpr ha⟩,hap⟩
  have hI : I = Finset.univ.filter (fun i =>
      0 < μ.sum (fun T k => k * Multiset.count i (T : Multiset ι))) := by
    ext i
    simp only [I,Multiset.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,
      ← Multiset.count_pos,V,M,count_vertices]
  have hle : Fintype.card I ≤ Fintype.card (ZMod (3^r+1) × ZMod (3^r+1)) := by
    simpa only [Fintype.card_coe,hI,Fintype.card_prod,ZMod.card,pow_two] using hcard
  let e : I ≃ ZMod (3^r+1) × ZMod (3^r+1) := Equiv.ofBijective toClass
    ⟨(Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq (Nat.le_antisymm hle (Fintype.card_le_of_surjective _ hsurj)))).mpr hsurj,
      hsurj⟩
  let ν : ∀ p,{a // cls a = p} := fun p => ⟨(e.symm p).val,e.apply_symm_apply p⟩
  have hchoice (a) (ha : a ∈ V) : (ν (cls a)).val = a := by
    have hh := congrArg Subtype.val (e.symm_apply_apply ⟨a,Multiset.mem_toFinset.mpr ha⟩)
    exact hh
  have htriple (T) (hT : T ∈ M) : T = assignTriple cls ν (f T) := by
    have hh := congrArg (Sym.map (fun p => (ν p).val)) (hf T hT)
    rw [Sym.map_map] at hh
    have hl : Sym.map (fun a => (ν (cls a)).val) T = T := by
      calc
        _ = Sym.map (fun a => a) T := Sym.map_congr (fun a ha =>
          hchoice a (Multiset.mem_bind.mpr ⟨T,hT,ha⟩))
        _ = T := Sym.map_id' T
    change Sym.map (fun a => (ν (cls a)).val) T = _ at hh
    rw [hl] at hh
    simpa only [triangle,Sym.map_cons,assignTriple,
      show Sym.map (fun p => (ν p).val) (Sym.nil : Sym (ZMod (3^r+1) × ZMod (3^r+1)) 0) =
        Sym.nil from Subsingleton.elim _ _] using hh
  have hB : M.map f = (Finset.univ : Finset (ZMod (3^r+1) × ZMod (3^r+1))).val := by
    apply Multiset.ext.mpr
    intro p
    rw [hcounts]
    simp
  have hM : M = (Finset.univ : Finset (ZMod (3^r+1) × ZMod (3^r+1))).val.map
      (assignTriple cls ν) := by
    rw [← hB,Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id' M]
    apply Multiset.map_congr rfl
    exact htriple
  refine ⟨ν,?_⟩
  apply Multiset.toFinsupp.symm.injective
  change M = Finsupp.toMultiset (assignMonomial cls ν)
  rw [hM,assignMonomial,map_sum]
  simp only [Finsupp.toMultiset_single,one_nsmul]
  simpa only [Finset.sum,Multiset.map_map,Function.comp_def] using
    (Multiset.sum_map_singleton
      ((Finset.univ : Finset (ZMod (3^r+1) × ZMod (3^r+1))).val.map (assignTriple cls ν))).symm

lemma assignment_multiset {m : ℕ} [NeZero m] {ι : Type}
    (cls : ι → ZMod m × ZMod m) (ν : ∀ p,{a // cls a = p}) :
    (assignMonomial cls ν).toMultiset =
      (Finset.univ : Finset (ZMod m × ZMod m)).val.map (assignTriple cls ν) := by
  classical
  rw [assignMonomial,map_sum]
  simp only [Finsupp.toMultiset_single,one_nsmul]
  simpa only [Finset.sum,Multiset.map_map,Function.comp_def] using
    Multiset.sum_map_singleton
      ((Finset.univ : Finset (ZMod m × ZMod m)).val.map (assignTriple cls ν))

lemma assignment_vertex {m : ℕ} [NeZero m] {ι : Type}
    (cls : ι → ZMod m × ZMod m) (ν : ∀ p,{a // cls a = p}) (p) :
    (ν p).val ∈ (assignMonomial cls ν).toMultiset.bind (fun T => (T : Multiset ι)) := by
  rw [assignment_multiset]
  apply Multiset.mem_bind.mpr
  refine ⟨assignTriple cls ν p,Multiset.mem_map.mpr ⟨p,Finset.mem_univ p,rfl⟩,?_⟩
  simp [assignTriple,Sym.coe_cons]

lemma assignment_vertex_choice {m : ℕ} [NeZero m] {ι : Type}
    (cls : ι → ZMod m × ZMod m) (ν : ∀ p,{a // cls a = p}) (a)
    (ha : a ∈ (assignMonomial cls ν).toMultiset.bind (fun T => (T : Multiset ι))) :
    (ν (cls a)).val = a := by
  rw [assignment_multiset] at ha
  obtain ⟨T,hT,ha⟩ := Multiset.mem_bind.mp ha
  obtain ⟨p,_,rfl⟩ := Multiset.mem_map.mp hT
  simp only [assignTriple,Sym.coe_cons,Sym.coe_nil,Multiset.mem_cons] at ha
  simp at ha
  rcases ha with ha | ha | ha
  · rw [ha,(ν p).property]
  · rw [ha,(ν (gridRight p)).property]
  · rw [ha,(ν (gridDown p)).property]

theorem assignment_injective {m : ℕ} [NeZero m] {ι : Type}
    (cls : ι → ZMod m × ZMod m) : Function.Injective (assignMonomial cls) := by
  intro ν η h
  funext p
  apply Subtype.ext
  have ha := assignment_vertex cls ν p
  rw [h] at ha
  have hc := assignment_vertex_choice cls η (ν p).val ha
  rw [(ν p).property] at hc
  exact hc.symm

lemma assignment_eval {m : ℕ} [NeZero m] {ι S : Type} [CommRing S]
    (cls : ι → ZMod m × ZMod m) (ν : ∀ p,{a // cls a = p}) (A : Sym ι 3 → S) :
    (assignMonomial cls ν).prod (fun T k => A T ^ k) =
      ∏ p,A (assignTriple cls ν p) := by
  classical
  rw [assignMonomial,← Finsupp.prod_finsetSum_index (by intros; simp)
    (by intros; exact pow_add _ _ _)]
  apply Finset.prod_congr rfl
  intro p _
  simp

theorem extraction_of_common_coefficient (𝓡 : ResultantSystem) (r : ℕ) (hr : 1 ≤ r)
    (n : ℕ) (κ : ℤ) (hκ : κ ≠ 0)
    (cls : Fin n → ZMod (3^r+1) × ZMod (3^r+1)) (hcls : Function.Surjective cls)
    (hcoeff : ∀ ν : (∀ p,{a // cls a = p}),
      (charCoeff 𝓡 n ((3^r+1)^2)).coeff (assignMonomial cls ν) = κ)
    (S : Type) [CommRing S] (A : Sym (Fin n) 3 → S) (hA : SupportedOnGrid cls A) :
    MvPolynomial.aeval A (charCoeff 𝓡 n ((3^r+1)^2)) = (κ : S) * gridSum cls A := by
  classical
  let P := charCoeff 𝓡 n ((3^r+1)^2)
  let assignments := (Finset.univ : Finset (∀ p,{a // cls a = p})).image (assignMonomial cls)
  have hn : 1 ≤ n := by
    obtain ⟨i,_⟩ := hcls (0,0)
    have := i.isLt
    omega
  have hsub : assignments ⊆ P.support := by
    intro μ hμ
    obtain ⟨ν,_,rfl⟩ := Finset.mem_image.mp hμ
    exact MvPolynomial.mem_support_iff.mpr ((hcoeff ν).symm ▸ hκ)
  have hzero (μ) (hμ : μ ∈ P.support) (hnm : μ ∉ assignments) :
      ((P.coeff μ : ℤ) : S) * μ.prod (fun T k => A T ^ k) = 0 := by
    by_cases hz : ∃ T ∈ μ.support,A T = 0
    · obtain ⟨T,hT,hAT⟩ := hz
      have hp : μ.prod (fun T k => A T ^ k) = 0 := by
        apply Finset.prod_eq_zero hT
        change A T ^ μ T = 0
        rw [hAT]
        exact zero_pow (Finsupp.mem_support_iff.mp hT)
      rw [hp,mul_zero]
    · exfalso
      have hgood (T) (hT : T ∈ μ.support) : ∃ p,Sym.map cls T = triangle p :=
        supported_classes cls A hA T (fun h => hz ⟨T,hT,h⟩)
      have hdeg := (CharacteristicHomogeneity.charCoeff_homogeneous 𝓡 n ((3^r+1)^2)).degree_eq_sum_deg_support hμ
      obtain ⟨hd,hc⟩ := ResultantVNP.lemma_3_4 𝓡 hn ((3^r+1)^2) μ hμ
      obtain ⟨ν,hν⟩ := assignment_of_monomial r hr cls μ hdeg.symm hd hc hgood
      exact hnm (Finset.mem_image.mpr ⟨ν,Finset.mem_univ _,hν.symm⟩)
  rw [MvPolynomial.aeval_def,MvPolynomial.eval₂_eq]
  change (∑ μ ∈ P.support,((P.coeff μ : ℤ) : S) * μ.prod (fun T k => A T ^ k)) = _
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_image]
  · dsimp only [P]
    simp_rw [hcoeff,assignment_eval]
    rw [← Finset.mul_sum]
    rfl
  · intro ν _ η _ h
    exact assignment_injective cls h

end GridExtraction

theorem solution (𝓡 : ResultantVNP.ResultantSystem) (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    ∃ κ : ℤ, κ ≠ 0 ∧
      (∀ cls : Fin n → ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1), Function.Surjective cls →
        ∀ ν : (∀ p, {α // cls α = p}),
          (ResultantVNP.charCoeff 𝓡 n ((3 ^ r + 1) ^ 2)).coeff (ResultantVNP.assignMonomial cls ν) = κ) ∧
      ∀ cls : Fin n → ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1), Function.Surjective cls →
        ∀ (S : Type) [CommRing S] (A : Sym (Fin n) 3 → S), ResultantVNP.SupportedOnGrid cls A →
          MvPolynomial.aeval A (ResultantVNP.charCoeff 𝓡 n ((3 ^ r + 1) ^ 2)) =
            (κ : S) * ResultantVNP.gridSum cls A := by
  have hm : 3 ≤ 3^r+1 := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 3 by decide) hr
    norm_num at h
    omega
  obtain ⟨κ,hκ,hcoeff⟩ := ResultantVNP.theorem_3_5 𝓡 (3^r+1) hm n
  refine ⟨κ,hκ,hcoeff,?_⟩
  intro cls hcls S _ A hA
  exact GridExtraction.extraction_of_common_coefficient 𝓡 r hr n κ hκ cls hcls
    (hcoeff cls hcls) S A hA

#print axioms GridExtraction.assignment_of_monomial
#print axioms GridExtraction.assignment_injective
#print axioms GridExtraction.extraction_of_common_coefficient
#print axioms solution

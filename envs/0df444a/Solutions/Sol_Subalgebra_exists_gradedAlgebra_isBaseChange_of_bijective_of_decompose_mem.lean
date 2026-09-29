-- Prove2me | solution 1 for Subalgebra.exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/81166951-7f68-5f44-9a16-27f70c49d895

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem

set_option autoImplicit false

open TensorProduct DirectSum

universe u

namespace GradedDescent

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
  (𝒜' : ℕ → Submodule S' A') [GradedAlgebra 𝒜']
  (A : Subalgebra S A')

def 𝒜 (n : ℕ) : Submodule S A := ((𝒜' n).restrictScalars S).comap A.val.toLinearMap

theorem mem_𝒜 {n : ℕ} {a : A} : a ∈ 𝒜 S' A' 𝒜' A n ↔ (a : A') ∈ 𝒜' n := Iff.rfl

scoped instance gradedMonoid : SetLike.GradedMonoid (𝒜 S' A' 𝒜' A) where
  one_mem := by rw [mem_𝒜]; exact SetLike.one_mem_graded 𝒜'
  mul_mem := fun i j a b ha hb => by
    rw [mem_𝒜] at ha hb ⊢
    rw [Subalgebra.coe_mul]
    exact SetLike.mul_mem_graded ha hb

variable (hhom : ∀ a ∈ A, ∀ n : ℕ, (DirectSum.decompose 𝒜' a n : A') ∈ A)

include hhom in
private theorem _root_.GradedDescent.isInternal : DirectSum.IsInternal (𝒜 S' A' 𝒜' A) := by
  classical
  constructor
  ·
    intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    set z := x - y with hz
    have hz0 : DirectSum.coeAddMonoidHom (𝒜 S' A' 𝒜' A) z = 0 := by rw [hz, map_sub]; exact hxy

    let ι' : ∀ i, 𝒜 S' A' 𝒜' A i →+ 𝒜' i := fun i =>
      { toFun := fun a => ⟨(a.1 : A'), a.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let T : (⨁ i, 𝒜 S' A' 𝒜' A i) →+ ⨁ i, 𝒜' i := DirectSum.toAddMonoid fun i => (DirectSum.of _ i).comp (ι' i)
    have hT : ∀ w, DirectSum.coeAddMonoidHom 𝒜' (T w) = ((DirectSum.coeAddMonoidHom (𝒜 S' A' 𝒜' A) w : A) : A') := by
      intro w
      induction w using DirectSum.induction_on with
      | zero => simp
      | of i a => simp [T, ι', DirectSum.toAddMonoid_of, DirectSum.coeAddMonoidHom_of]
      | add a b ha hb => simp only [map_add, ha, hb, Subalgebra.coe_add]
    have hTz : T z = 0 := by
      apply (DirectSum.Decomposition.isInternal 𝒜').1
      rw [hT, hz0, map_zero]; rfl

    apply DFinsupp.ext
    intro i
    have := DFinsupp.ext_iff.mp hTz i
    have hcomp : ∀ w i, (T w) i = ι' i (w i) := by
      intro w i
      induction w using DirectSum.induction_on with
      | zero => simp [ι']; rfl
      | of j a =>
        simp only [T, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
        by_cases h : j = i
        · subst h; simp [DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne j i _ (Ne.symm h), DirectSum.of_eq_of_ne j i _ (Ne.symm h), map_zero]
      | add a b ha hb => simp only [map_add, DirectSum.add_apply, ha, hb]
    rw [hcomp] at this
    have h2 : ((z i : A) : A') = 0 := by
      have h3 := congrArg Subtype.val this
      simpa [ι'] using h3
    rw [DirectSum.zero_apply]
    exact Subtype.ext (Subtype.ext (by simpa using h2))
  ·
    intro a
    refine ⟨∑ i ∈ (DirectSum.decompose 𝒜' (a : A')).support,
      DirectSum.of (fun i => ↥(𝒜 S' A' 𝒜' A i)) i ⟨⟨(DirectSum.decompose 𝒜' (a : A') i : A'), hhom a a.2 i⟩,
        (DirectSum.decompose 𝒜' (a : A') i).2⟩, ?_⟩
    rw [map_sum]
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜' (a : A')]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DirectSum.coeAddMonoidHom_of]

p2m_export "GradedDescent" "isInternal"

@[reducible] noncomputable def gradedAlgebra : GradedAlgebra (𝒜 S' A' 𝒜' A) :=
  { (isInternal S' A' 𝒜' A hhom).chooseDecomposition with }

theorem coe_decompose (a : A) (n : ℕ) :
    letI := gradedAlgebra S' A' 𝒜' A hhom
    (((DirectSum.decompose (𝒜 S' A' 𝒜' A) a n : A) : A') = (DirectSum.decompose 𝒜' (a : A') n : A')) := by
  classical
  letI := gradedAlgebra S' A' 𝒜' A hhom

  have h := DirectSum.sum_support_decompose (𝒜 S' A' 𝒜' A) a
  have h' : (a : A') = ∑ i ∈ (DirectSum.decompose (𝒜 S' A' 𝒜' A) a).support,
      (((DirectSum.decompose (𝒜 S' A' 𝒜' A) a i : A) : A')) := by
    rw [← AddSubmonoidClass.coe_finsetSum]
    exact congrArg Subtype.val h.symm
  conv_rhs => rw [← GradedAlgebra.proj_apply, h', map_sum]
  have key : ∀ i, GradedAlgebra.proj 𝒜' n (((DirectSum.decompose (𝒜 S' A' 𝒜' A) a i : A) : A')) =
      if i = n then (((DirectSum.decompose (𝒜 S' A' 𝒜' A) a i : A) : A')) else 0 := by
    intro i
    rw [GradedAlgebra.proj_apply]
    have hmem : (((DirectSum.decompose (𝒜 S' A' 𝒜' A) a i : A) : A')) ∈ 𝒜' i :=
      (DirectSum.decompose (𝒜 S' A' 𝒜' A) a i).2
    split_ifs with hi
    · subst hi; exact DirectSum.decompose_of_mem_same 𝒜' hmem
    · exact DirectSum.decompose_of_mem_ne 𝒜' hmem hi
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · simp [DFinsupp.notMem_support_iff.mp hn]

section BaseChange

theorem h𝒜 (n : ℕ) : ∀ a ∈ 𝒜 S' A' 𝒜' A n, A.val a ∈ 𝒜' n := fun _ ha => ha

abbrev valn (n : ℕ) : 𝒜 S' A' 𝒜' A n →ₗ[S] (𝒜' n).restrictScalars S :=
  A.val.toLinearMap.restrict (p := 𝒜 S' A' 𝒜' A n) (q := (𝒜' n).restrictScalars S) (h𝒜 S' A' 𝒜' A n)

abbrev G : S' ⊗[S] A →ₐ[S] A' :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun _ _ => Commute.all _ _)

theorem G_tmul (s : S') (a : A) : G S' A' A (s ⊗ₜ[S] a) = s • (a : A') := by
  rw [Algebra.TensorProduct.lift_tmul, IsScalarTower.coe_toAlgHom', Algebra.smul_def]; rfl

noncomputable abbrev gn (n : ℕ) : S' ⊗[S] ↥(𝒜 S' A' 𝒜' A n) →ₗ[S'] ↥((𝒜' n).restrictScalars S) :=
  (valn S' A' 𝒜' A n).liftBaseChange S'

theorem coe_gn (n : ℕ) (z : S' ⊗[S] ↥(𝒜 S' A' 𝒜' A n)) :
    ((gn S' A' 𝒜' A n z : ↥((𝒜' n).restrictScalars S)) : A') =
      G S' A' A (LinearMap.lTensor S' (𝒜 S' A' 𝒜' A n).subtype z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s x =>
    rw [LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, G_tmul]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, Submodule.coe_add, hx, hy]

include hhom in

theorem exists_retraction (n : ℕ) :
    ∃ r : A →ₗ[S] ↥(𝒜 S' A' 𝒜' A n), (∀ x : ↥(𝒜 S' A' 𝒜' A n), r x = x) ∧
      ∀ a : A, ((r a : A) : A') = (DirectSum.decompose 𝒜' (a : A') n : A') := by
  classical
  letI := gradedAlgebra S' A' 𝒜' A hhom
  refine ⟨(DirectSum.component S ℕ (fun i => ↥(𝒜 S' A' 𝒜' A i)) n) ∘ₗ
    (DirectSum.decomposeLinearEquiv (𝒜 S' A' 𝒜' A)).toLinearMap, fun x => ?_, fun a => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, DirectSum.decomposeLinearEquiv_apply]
    rw [DirectSum.decompose_coe, ← DirectSum.apply_eq_component, DirectSum.of_eq_same]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, DirectSum.decomposeLinearEquiv_apply]
    rw [← coe_decompose S' A' 𝒜' A hhom a n]
    rfl

include hhom in
theorem bijective_gn (hbij : Function.Bijective (G S' A' A)) (n : ℕ) : Function.Bijective (gn S' A' 𝒜' A n) := by
  obtain ⟨r, hr, hr'⟩ := exists_retraction S' A' 𝒜' A hhom n
  have hrj : r ∘ₗ (𝒜 S' A' 𝒜' A n).subtype = LinearMap.id := LinearMap.ext hr

  have hproj : ∀ z : S' ⊗[S] A,
      G S' A' A (LinearMap.lTensor S' ((𝒜 S' A' 𝒜' A n).subtype ∘ₗ r) z) =
        GradedAlgebra.proj 𝒜' n (G S' A' A z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      rw [LinearMap.lTensor_tmul, G_tmul, G_tmul, LinearMap.map_smul, GradedAlgebra.proj_apply, ← hr' a]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  constructor
  · intro z₁ z₂ h
    rw [← sub_eq_zero] at h ⊢
    rw [← map_sub] at h
    set z := z₁ - z₂
    have h1 : G S' A' A (LinearMap.lTensor S' (𝒜 S' A' 𝒜' A n).subtype z) = 0 := by
      rw [← coe_gn, h]; rfl
    have h2 : LinearMap.lTensor S' (𝒜 S' A' 𝒜' A n).subtype z = 0 :=
      hbij.1 (by rw [h1, map_zero])
    have h3 := congrArg (LinearMap.lTensor S' r) h2
    rwa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hrj, LinearMap.lTensor_id, map_zero,
      LinearMap.id_apply] at h3
  · intro b
    obtain ⟨z, hz⟩ := hbij.2 (b : A')
    refine ⟨LinearMap.lTensor S' r z, ?_⟩
    apply Subtype.ext
    rw [coe_gn, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hproj, hz, GradedAlgebra.proj_apply]
    exact DirectSum.decompose_of_mem_same 𝒜' b.2

include hhom in
theorem isBaseChange (hbij : Function.Bijective (G S' A' A)) (n : ℕ) : IsBaseChange S' (valn S' A' 𝒜' A n) :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective (gn S' A' 𝒜' A n) (bijective_gn S' A' 𝒜' A hhom hbij n))
    (fun x => by simp [LinearMap.liftBaseChange_tmul])

end BaseChange

end GradedDescent
p2m_reactivate "P2MW.S_Subalgebra_exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem.GradedDescent"

open GradedDescent in
theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (𝒜' : ℕ → Submodule S' A') [GradedAlgebra 𝒜']
    (A : Subalgebra S A')
    (hbij : Function.Bijective
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun _ _ => Commute.all _ _)))
    (hhom : ∀ a ∈ A, ∀ n : ℕ, (DirectSum.decompose 𝒜' a n : A') ∈ A) :
    ∃ (𝒜 : ℕ → Submodule S A) (_ : GradedAlgebra 𝒜) (h𝒜 : ∀ n, ∀ a ∈ 𝒜 n, A.val a ∈ 𝒜' n),
      (∀ (n : ℕ) (a : A), (a : A') ∈ 𝒜' n → a ∈ 𝒜 n) ∧
      (∀ n, IsBaseChange S' ((A.val.toLinearMap.restrict (p := 𝒜 n) (q := (𝒜' n).restrictScalars S) (h𝒜 n))
        : 𝒜 n →ₗ[S] (𝒜' n).restrictScalars S)) ∧
      HomogeneousIdeal.irrelevant 𝒜' ≤
        (HomogeneousIdeal.irrelevant 𝒜).map ({ A.val.toRingHom with map_mem := fun h => h𝒜 _ _ h } : 𝒜 →+*ᵍ 𝒜') := by
  classical
  refine ⟨GradedDescent.𝒜 S' A' 𝒜' A, gradedAlgebra S' A' 𝒜' A hhom, GradedDescent.h𝒜 S' A' 𝒜' A, fun n a ha => ha,
    fun n => isBaseChange S' A' 𝒜' A hhom hbij n, ?_⟩
  letI := gradedAlgebra S' A' 𝒜' A hhom
  intro x hx
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_map]
  rw [← DirectSum.sum_support_decompose 𝒜' x]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hi0 : i = 0
  · subst hi0
    rw [hx]
    exact Ideal.zero_mem _
  · have key : ∀ y : ↥((𝒜' i).restrictScalars S),
        (y : A') ∈ Ideal.map ({ A.val.toRingHom with map_mem := fun h => GradedDescent.h𝒜 S' A' 𝒜' A _ _ h } :
          GradedDescent.𝒜 S' A' 𝒜' A →+*ᵍ 𝒜') (HomogeneousIdeal.irrelevant (GradedDescent.𝒜 S' A' 𝒜' A)).toIdeal := by
      intro y
      induction y using (isBaseChange S' A' 𝒜' A hhom hbij i).inductionOn with
      | zero => simp
      | tmul m =>
        refine Ideal.mem_map_of_mem _ ?_
        rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
        exact DirectSum.decompose_of_mem_ne _ m.2 hi0
      | smul s y hy =>
        change s • (y : A') ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hy
      | add y₁ y₂ h₁ h₂ =>
        change (y₁ : A') + (y₂ : A') ∈ _
        exact Ideal.add_mem _ h₁ h₂
    exact key ⟨_, (DirectSum.decompose 𝒜' x i).2⟩

end S_Subalgebra_exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem
end P2MW
export P2MW.S_Subalgebra_exists_gradedAlgebra_isBaseChange_of_bijective_of_decompose_mem (solution)

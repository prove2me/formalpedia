-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.primeHeckeSet_eq_and_heckeKernel_eq_of_ramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/00f935da-35bd-5a20-99b2-6ab3deb2ce6d

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_primeHeckeSet_eq_and_heckeKernel_eq_of_ramified
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace RamHeckePI

variable {a b : ℚ}

theorem setOf_mul_eq_of_mem
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (π ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hT : T = {h | ∃ u ∈ U, h = π * u}) (hϖ : ϖ ∈ T) :
    T = {h | ∃ u ∈ U, h = ϖ * u} := by
  rw [hT] at hϖ ⊢
  obtain ⟨u₁, hu₁, rfl⟩ := hϖ
  ext h
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u₁⁻¹ * u, mul_mem (inv_mem hu₁) hu, by group⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u₁ * u, mul_mem hu₁ hu, by rw [mul_assoc]⟩

theorem classSetShift_eq_of_mem
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (π ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hϖ : ∃ u ∈ U, ϖ = π * u) (x : QuaternionAlgebra.ClassSet U) :
    CerednikDrinfeld.classSetShift U ϖ x = CerednikDrinfeld.classSetShift U π x := by
  obtain ⟨u₁, hu₁, rfl⟩ := hϖ
  unfold CerednikDrinfeld.classSetShift
  rw [← mul_assoc, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ hu₁]

theorem heckeKernel_eq_ite
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [DecidableEq (QuaternionAlgebra.ClassSet U)]
    (hM : CerednikDrinfeld.classSetHeckeMatrix U T =
      Matrix.of (fun i j : QuaternionAlgebra.ClassSet U =>
        if CerednikDrinfeld.classSetShift U π j = i then (1 : ℤ) else 0))
    (x y : QuaternionAlgebra.ClassSet U) :
    QuaternionAlgebra.heckeKernel U T x y = if CerednikDrinfeld.classSetShift U π x = y then 1 else 0 := by
  have h := congrFun (congrFun hM y) x
  unfold CerednikDrinfeld.classSetHeckeMatrix at h
  simpa only [Matrix.of_apply] using h

theorem classSetShift_mk
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hnorm : ∀ u ∈ U, π⁻¹ * u * π ∈ U)
    (z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetShift U π (QuaternionAlgebra.ClassSet.mk U z) =
      QuaternionAlgebra.ClassSet.mk U (z * π) := by
  unfold CerednikDrinfeld.classSetShift
  obtain ⟨δ, k, hδ, hk, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U z
  obtain ⟨d', rfl⟩ := MonoidHom.mem_range.mp hδ
  rw [show (QuaternionAlgebra.ClassSet.mk U z).out = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d' * z * k from hout]
  have e1 : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d' * z * k * π =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d' * (z * π * (π⁻¹ * k * π)) := by group
  rw [e1, QuaternionAlgebra.ClassSet.mk_diagonal_mul, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ (hnorm k hk)]

theorem classSetShift_classSetShift
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hnorm : ∀ u ∈ U, π⁻¹ * u * π ∈ U)
    (d : (ℍ[ℚ, a, b])ˣ) (u₀ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu₀ : u₀ ∈ U)
    (hππ : π * π = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * u₀)
    (hcentral : ∀ g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * g = g * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d)
    (x : QuaternionAlgebra.ClassSet U) :
    CerednikDrinfeld.classSetShift U π (CerednikDrinfeld.classSetShift U π x) = x := by
  obtain ⟨z, rfl⟩ := QuaternionAlgebra.ClassSet.mk_surjective x
  rw [classSetShift_mk U π hnorm, classSetShift_mk U π hnorm, mul_assoc, hππ, ← mul_assoc, ← hcentral, mul_assoc,
    QuaternionAlgebra.ClassSet.mk_diagonal_mul, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ hu₀]

theorem mulVec_of_ite_eq_comp {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ι) (hs : ∀ i, s (s i) = i)
    (f : ι → ℤ) :
    (Matrix.of (fun i j : ι => if s j = i then (1 : ℤ) else 0)).mulVec f = f ∘ s := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (s i)]
  · rw [if_pos (hs i), one_mul]
  · intro j _ hj
    rw [if_neg, zero_mul]
    intro hji
    exact hj (by rw [← hji, hs j])
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem main {p : ℕ} [Fact p.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    {X : Submodule ℤ ℍ[ℚ, a, b]} {M : ℕ} (hX : QuaternionAlgebra.IsEichlerOrder X M)
    (ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hϖ : ϖ ∈ QuaternionAlgebra.primeHeckeSet X p) :
    QuaternionAlgebra.primeHeckeSet X p =
      {h | ∃ u ∈ Submodule.finiteIdeleStabilizer X, h = ϖ * u} ∧
    (∀ x y : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer X),
      (CerednikDrinfeld.classSetShift _ ϖ x = y →
        QuaternionAlgebra.heckeKernel (Submodule.finiteIdeleStabilizer X) (QuaternionAlgebra.primeHeckeSet X p) x y = 1) ∧
      (CerednikDrinfeld.classSetShift _ ϖ x ≠ y →
        QuaternionAlgebra.heckeKernel (Submodule.finiteIdeleStabilizer X) (QuaternionAlgebra.primeHeckeSet X p) x y = 0)) ∧
    ∀ [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer X))]
      (f : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer X) → ℤ),
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer X)
        (QuaternionAlgebra.primeHeckeSet X p)).mulVec f =
        f ∘ CerednikDrinfeld.classSetShift _ ϖ := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨π, hπT, -, hnorm', ⟨u₀, hu₀, hππ⟩, hT, hM, -⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt hp hdef hX
  set U := Submodule.finiteIdeleStabilizer X with hU
  set T := QuaternionAlgebra.primeHeckeSet X p with hTdef

  have hϖπ : ∃ u ∈ U, ϖ = π * u := by
    have h : ϖ ∈ {h | ∃ u ∈ U, h = π * u} := hT ▸ hϖ
    exact h
  have hshift : ∀ x, CerednikDrinfeld.classSetShift U ϖ x = CerednikDrinfeld.classSetShift U π x :=
    classSetShift_eq_of_mem U π ϖ hϖπ

  have hnorm : ∀ u ∈ U, π⁻¹ * u * π ∈ U := by
    intro u hu
    refine (hnorm' (π⁻¹ * u * π)).mpr ?_
    have e : π * (π⁻¹ * u * π) * π⁻¹ = u := by group
    rwa [e]

  set d : (ℍ[ℚ, a, b])ˣ :=
    Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) with hd
  have hdval : ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      algebraMap ℚ (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) (p : ℚ) := by
    rw [Submodule.val_finiteIdeleDiagonal_apply, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hcentral : ∀ g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * g = g * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d := by
    intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hdval]
    exact Algebra.commutes _ _
  have hinv : ∀ x, CerednikDrinfeld.classSetShift U π (CerednikDrinfeld.classSetShift U π x) = x :=
    classSetShift_classSetShift U π hnorm d u₀ hu₀ hππ hcentral
  refine ⟨setOf_mul_eq_of_mem U T π ϖ hT hϖ, fun x y => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [heckeKernel_eq_ite U T π hM x y, if_pos (by rwa [← hshift])]
  · rw [heckeKernel_eq_ite U T π hM x y, if_neg (by rwa [← hshift])]
  · intro _ f
    have hM' : CerednikDrinfeld.classSetHeckeMatrix U T =
        Matrix.of (fun i j : QuaternionAlgebra.ClassSet U =>
          if CerednikDrinfeld.classSetShift U π j = i then (1 : ℤ) else 0) := by
      convert hM using 1
    rw [hM', mulVec_of_ite_eq_comp (CerednikDrinfeld.classSetShift U π) hinv f]
    funext i
    simp only [Function.comp_apply, hshift]

end RamHeckePI

end

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {X : Submodule ℤ ℍ[ℚ, a, b]} {M : ℕ} (hX : IsEichlerOrder X M)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hϖ : ϖ ∈ primeHeckeSet X p) :
    primeHeckeSet X p =
      {h | ∃ u ∈ Submodule.finiteIdeleStabilizer X, h = ϖ * u} ∧
    (∀ x y : ClassSet (Submodule.finiteIdeleStabilizer X),
      (classSetShift _ ϖ x = y → heckeKernel (Submodule.finiteIdeleStabilizer X) (primeHeckeSet X p) x y = 1) ∧
      (classSetShift _ ϖ x ≠ y → heckeKernel (Submodule.finiteIdeleStabilizer X) (primeHeckeSet X p) x y = 0)) ∧
    ∀ [Fintype (ClassSet (Submodule.finiteIdeleStabilizer X))] (f : ClassSet (Submodule.finiteIdeleStabilizer X) → ℤ),
      (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer X) (primeHeckeSet X p)).mulVec f =
        f ∘ classSetShift _ ϖ :=
  RamHeckePI.main hdef hX ϖ hϖ

end S_QuaternionAlgebra_IsEichlerOrder_primeHeckeSet_eq_and_heckeKernel_eq_of_ramified
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_primeHeckeSet_eq_and_heckeKernel_eq_of_ramified (solution)

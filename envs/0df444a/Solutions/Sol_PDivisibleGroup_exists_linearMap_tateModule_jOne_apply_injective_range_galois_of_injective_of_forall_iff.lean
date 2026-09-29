-- Prove2me | solution 1 for PDivisibleGroup.exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f951d760-594a-5f85-9564-1976fc22d538

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_TateModule

import Theorems.Thm_TateModule_exists_linearMap_apply_eq_of_addMonoidHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (A : Type) [CommRing A] [Algebra A (AlgebraicClosure ℚ)]
    {h : ℕ} (𝒢 : PDivisibleGroup A p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JOne (M * p))
    (hF1 : Function.Injective Δ)
    (hLEV : (∀ (v : ℕ) (y : ModularCurve.JOne (M * p)),
          ((p ^ v) • y = 0 ∧ y ∈ ModularCurve.normFreePartAt (M * p) p) ↔
          ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y))
    (hGAL : (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[A] AlgebraicClosure ℚ),
          (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)) :
    ∃ e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne (M * p)),
      (∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
        ((e x : TateModule p (ModularCurve.JOne (M * p))) : ℕ → ModularCurve.JOne (M * p)) n =
          Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n)) ∧
      Function.Injective e ∧
      (∀ y : TateModule p (ModularCurve.JOne (M * p)), y ∈ LinearMap.range e ↔
        ∀ n : ℕ, (y : ℕ → ModularCurve.JOne (M * p)) n ∈ ModularCurve.normFreePartAt (M * p) p) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[A] AlgebraicClosure ℚ),
        (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
        ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
          e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) =
            TateModule.rep p (ModularCurve.JOne (M * p)) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ (e x)) := by
  classical
  obtain ⟨e, he, hinj⟩ := TateModule.exists_linearMap_apply_eq_of_addMonoidHom p Δ

  have hΔA : ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ z ∈ ModularCurve.normFreePartAt (M * p) p := by
    intro z
    obtain ⟨v, x, rfl⟩ := PDivisibleGroup.Points.exists_mkAdd (G := 𝒢) (L := AlgebraicClosure ℚ) z
    exact ((hLEV v _).mpr ⟨x, rfl⟩).2
  refine ⟨e, he, hinj hF1, ?_, ?_⟩
  ·
    intro y
    constructor
    · rintro ⟨x, rfl⟩ n
      rw [he]
      exact hΔA _
    · intro hy

      have hex : ∀ n : ℕ, ∃ x : 𝒢.Point (AlgebraicClosure ℚ) n,
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) n (Additive.ofMul x)) = (y : ℕ → ModularCurve.JOne (M * p)) n := by
        intro n
        refine (hLEV n _).mp ⟨?_, hy n⟩
        have := TateModule.torsion y n
        rwa [← Nat.cast_smul_eq_nsmul ℤ]
      choose xs hxs using hex
      let x : ℕ → 𝒢.Points (AlgebraicClosure ℚ) := fun n => 𝒢.pointsMkAdd (AlgebraicClosure ℚ) n (Additive.ofMul (xs n))
      have hxmem : x ∈ TateModule p (𝒢.Points (AlgebraicClosure ℚ)) := by
        intro n
        constructor
        · show ((p ^ n : ℕ) : ℤ) • 𝒢.pointsMkAdd (AlgebraicClosure ℚ) n (Additive.ofMul (xs n)) = 0
          rw [Nat.cast_smul_eq_nsmul ℤ]
          exact PDivisibleGroup.nsmul_pointsMkAdd_eq_zero (G := 𝒢) (L := AlgebraicClosure ℚ) n (xs n)
        · apply hF1
          show Δ (((p : ℕ) : ℤ) • x (n + 1)) = Δ (x n)
          rw [map_zsmul, hxs, hxs]
          exact TateModule.compat y n
      refine ⟨⟨x, hxmem⟩, Subtype.ext (funext fun n => ?_)⟩
      rw [he]
      exact hxs n
  ·
    intro τ τ' hτ x
    apply Subtype.ext
    funext n
    rw [he, PDivisibleGroup.tateModuleRep_apply, TateModule.rep_apply, he]
    exact hGAL τ τ' hτ _

end S_PDivisibleGroup_exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff
end P2MW
export P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff (solution)

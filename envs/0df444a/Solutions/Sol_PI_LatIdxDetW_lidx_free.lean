-- Prove2me | solution 1 for PI.LatIdxDetW.lidx_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:14:30.930642+00:00
-- url     : https://prove2.me/submissions/88bb53e8-ff7b-4363-845a-92395d9f29d2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Theorems.Thm_PI_LatIdxDetW_lidx_map
import Theorems.Thm_Formalism_DivisionValues_indexChange_of_det_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [FiniteDimensional K V]
namespace PI.LatIdxDetW
theorem _root_.solution (w : HeightOneSpectrum R) {d : ℕ} (b : Basis (Fin d) K V) (γ : V ≃ₗ[K] V) :
    lidx w.asIdeal (Submodule.span R (Set.range b))
      ((Submodule.span R (Set.range b)).map ((γ.restrictScalars R : V ≃ₗ[R] V) : V →ₗ[R] V)) =
      FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton R⁰ (LinearMap.det (γ : V →ₗ[K] V))) := by
  classical
  let φ : V ≃ₗ[R] (Fin d → K) := b.equivFun.restrictScalars R
  let M := LinearMap.toMatrix b b (γ : V →ₗ[K] V)
  let e : Fin d → Fin d → K := fun i => φ (b i)
  have he : LinearIndependent K e := b.linearIndependent.map' b.equivFun.toLinearMap b.equivFun.ker
  have hact : Formalism.DivisionValues.idxChangeAct e M = fun i => φ (γ (b i)) := by
    funext i j
    simp [Formalism.DivisionValues.idxChangeAct, e, φ, M, LinearMap.toMatrix_apply, Finset.sum_apply, Finsupp.single_apply]
  have h1 : (Submodule.span R (Set.range b)).map (φ : V →ₗ[R] (Fin d → K)) =
      Submodule.span R (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have h2 : ((Submodule.span R (Set.range b)).map ((γ.restrictScalars R : V ≃ₗ[R] V) : V →ₗ[R] V)).map
      (φ : V →ₗ[R] (Fin d → K)) = Submodule.span R (Set.range (Formalism.DivisionValues.idxChangeAct e M)) := by
    rw [hact, Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hdet : M.det ≠ 0 := by
    rw [LinearMap.det_toMatrix]
    exact (LinearEquiv.isUnit_det' γ).ne_zero
  rw [← lidx_map w.asIdeal φ, h1, h2, Formalism.DivisionValues.indexChange_of_det_ne_zero w M hdet e he, LinearMap.det_toMatrix]
end PI.LatIdxDetW

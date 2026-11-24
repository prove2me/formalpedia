-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_det_fderiv_e2dfa5ad9526
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:09.542005+00:00
-- url     : https://prove2.me/submissions/9f5a365d-4ca1-461c-afa8-de4023050e00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HolomorphicZerosNotIsolated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {k : ℕ} {f : (Fin k → ℂ) → Fin k → ℂ} {x : Fin k → ℂ}
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) x := by
  have hd : AnalyticAt ℂ (fderiv ℂ f) x := hf.fderiv
  have he : ∀ i j : Fin k, AnalyticAt ℂ (fun z => fderiv ℂ f z (Pi.single j 1) i) x := by
    intro i j
    let L : ((Fin k → ℂ) →L[ℂ] Fin k → ℂ) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).comp
        (ContinuousLinearMap.apply ℂ (Fin k → ℂ) (Pi.single j 1))
    show AnalyticAt ℂ (L ∘ fderiv ℂ f) x
    exact (L.analyticAt _).comp hd
  have heq : (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) =
      fun z => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ f z (Pi.single i 1) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix', Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  rw [heq]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_differentiableOn_jac_fd06ac4187c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:54.634019+00:00
-- url     : https://prove2.me/submissions/39de2f0e-644e-4fc0-a3d5-2fc62eccf3db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperHolomorphicSurjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_analyticOnNhd_of_differentiableOn_860e95b7c849

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
open Topology Metric MeasureTheory
open scoped ENNReal NNReal
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperHolomorphicSurjective
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperHolomorphicSurjective
theorem _root_.solution {k : ℕ} {Ω : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → Fin k → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (jac g) Ω := by
  have hfd : DifferentiableOn ℂ (fderiv ℂ g) Ω :=
    (analyticOnNhd_of_differentiableOn hΩ hg).fderiv.differentiableOn
  have hentry : ∀ i j : Fin k,
      DifferentiableOn ℂ (fun v => fderiv ℂ g v (Pi.single j 1) i) Ω := fun i j =>
    differentiableOn_pi.1 (hfd.clm_apply (differentiableOn_const _)) i
  have hjac : jac g = fun v => ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ g v (Pi.single i 1) (σ i) := by
    funext v
    rw [jac, ← LinearMap.det_toMatrix', Matrix.det_apply']
    simp [LinearMap.toMatrix'_apply]
  rw [hjac]
  refine DifferentiableOn.fun_sum fun σ _ => (differentiableOn_const _).mul ?_
  intro x hx
  exact (HasFDerivWithinAt.finsetProd (u := Finset.univ)
    (g := fun i v => fderiv ℂ g v (Pi.single i 1) (σ i))
    fun i _ => ((hentry (σ i) i) x hx).hasFDerivWithinAt).differentiableWithinAt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperHolomorphicSurjective

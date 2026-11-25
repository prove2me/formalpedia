-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_hasStrictFDerivAt_equiv_cba9f8ca6ee6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:53.810815+00:00
-- url     : https://prove2.me/submissions/ac809b4a-5452-4468-88fa-deb72e3b53cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
namespace GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
theorem _root_.solution {n : ℕ} {Q : (Fin n → ℂ) → (Fin n → ℂ)} {u : Fin n → ℂ}
    (hQ : AnalyticAt ℂ Q u)
    (hd : LinearMap.det (fderiv ℂ Q u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), HasStrictFDerivAt Q (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) u := by
  refine ⟨(LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv, ?_⟩
  have h : ((LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv :
      (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ Q u := by
    ext1 w
    rfl
  rw [h]
  exact hQ.hasStrictFDerivAt
end GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds

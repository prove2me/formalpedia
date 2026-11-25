-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullbackBadImage_holds_det_restrictScalars_eq_zero_cf45d55885cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:39.088085+00:00
-- url     : https://prove2.me/submissions/c0d1f3f1-e003-4698-bebc-d53cc074eeef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DetRestrictScalarsEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter
open GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds
theorem _root_.solution {m : ℕ} (f : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (h : LinearMap.det (f : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = 0) :
    (f.restrictScalars ℝ).det = 0 := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
  show LinearMap.det ((f.restrictScalars ℝ : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) :
    (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)) = 0
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ((Submodule.ne_bot_iff _).mpr ⟨w, ?_, hw0⟩)
  simpa using hw
end GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds

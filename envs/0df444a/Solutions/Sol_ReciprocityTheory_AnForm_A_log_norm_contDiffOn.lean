-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.log_norm_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:38.401+00:00
-- url     : https://prove2.me/submissions/f771bc96-4934-4f39-870b-3d21a79af800

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {u : (Fin D → ℂ) → ℂ} (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => Real.log ‖u z‖) U := by
  have ha : AnalyticOnNhd ℂ u U := ReciprocityTheory.AnForm.Osgood.osgood D U u hU hu
  have hc : ContDiffOn ℝ ∞ u U := (ha.contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun z => ‖u z‖ ^ 2) U := (contDiff_norm_sq ℝ).comp_contDiffOn hc
  have h3 : ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * Real.log (‖u z‖ ^ 2)) U :=
    contDiffOn_const.mul (h2.log fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hu0 z hz)))
  refine h3.congr fun z _ => ?_
  rw [Real.log_pow]
  push_cast
  ring
end ReciprocityTheory.AnForm.A

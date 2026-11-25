-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.Hc_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:31.200274+00:00
-- url     : https://prove2.me/submissions/20812c69-3422-4392-b346-a0e4e0ae9f7b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ a b : ℂ) :
    Hc φ z w ζ a b = fderiv ℝ (fderiv ℝ φ) (z + ζ • w) (a • w) (b • w) := by
  simp [Hc, Pc, L0]
end ReciprocityTheory.AnForm.A.PshLap

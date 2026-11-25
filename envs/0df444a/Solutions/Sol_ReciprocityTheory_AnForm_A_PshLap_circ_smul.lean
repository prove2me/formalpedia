-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.circ_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:58.298485+00:00
-- url     : https://prove2.me/submissions/364d4319-abee-4ab3-b34b-d36bcdf54408

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
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (r θ : ℝ) (w : Fin D → ℂ) :
    circleMap 0 r θ • w = circleMap 0 1 θ • ((r:ℂ) • w) := by
  ext i
  simp [circleMap]
  ring
end ReciprocityTheory.AnForm.A.PshLap

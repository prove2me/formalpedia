-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_measurable_tangentGaussProfile_fdaff60c6dae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:22.300971+00:00
-- url     : https://prove2.me/submissions/c8307b6e-aec7-40aa-8de6-9a343519cf01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tangentGaussProfile_abs_bb11bcb29d10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tangentGaussProfile_antitoneOn_60715fa850a4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (n m : ℕ) : Measurable (tangentGaussProfile n m) := by
  have hψ : Antitone fun t : ℝ => tangentGaussProfile n m (max t 0) := fun a b hab =>
    tangentGaussProfile_antitoneOn n m (Set.mem_Ici.2 (le_max_right a 0))
      (Set.mem_Ici.2 (le_max_right b 0)) (max_le_max hab le_rfl)
  have h : tangentGaussProfile n m = fun r => tangentGaussProfile n m (max |r| 0) := by
    funext r
    rw [max_eq_left (abs_nonneg r), tangentGaussProfile_abs]
  rw [h]
  exact hψ.measurable.comp measurable_abs
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_withBot_enat_le_pred_3ed6693ab82f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:44.353185+00:00
-- url     : https://prove2.me/submissions/f2387054-6833-4f49-906d-6c3369b33d77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetTubeVolume

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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x) (h : x < (d : WithBot ℕ∞)) :
    0 < d ∧ x ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => simp at h
    | coe m =>
      have hm : m < d := by exact_mod_cast h
      refine ⟨by omega, ?_⟩
      rw [← WithBot.coe_natCast]
      exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : m ≤ d - 1))
end GroundTheory.Heights₂.Heights

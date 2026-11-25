-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_TelescopeMetric_le_first_1c77e4a9049b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:38.947717+00:00
-- url     : https://prove2.me/submissions/16fee61d-bcb2-44b4-92e3-84c5cd34ba71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PTelescopeMetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace TelescopeMetric
theorem _root_.solution {n : ℕ} {I : ℕ → ℝ} (h : ∀ i, i < n → I (i + 1) ≤ I i) :
    ∀ i, i ≤ n → I i ≤ I 0 := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ k ih =>
    intro hk
    exact (h k (by omega)).trans (ih (by omega))
end TelescopeMetric
end GroundTheory.Heights₂.Heights.LowerBound

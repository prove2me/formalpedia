-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_lt_max_zero_log_div_iff_c2c029cf849b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:42.345793+00:00
-- url     : https://prove2.me/submissions/a64bb88a-297b-4881-9fa7-4dfe0b43d7a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanLogPlus

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
open Real MeasureTheory Filter Topology Set
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.LowerBound
theorem _root_.solution {t r l : ℝ} (ht : 0 < t) (hr : 0 < r) (hl : 0 < l) :
    t < max 0 (log (r / l)) ↔ l < exp (-t) * r := by
  rw [lt_max_iff, lt_log_iff_exp_lt (div_pos hr hl), lt_div_iff₀ hl, exp_neg,
    ← div_eq_inv_mul, lt_div_iff₀ (exp_pos t), mul_comm l]
  constructor
  · rintro (h | h)
    · exact absurd h (not_lt.2 ht.le)
    · exact h
  · exact Or.inr
end GroundTheory.Heights₂.Heights.LowerBound

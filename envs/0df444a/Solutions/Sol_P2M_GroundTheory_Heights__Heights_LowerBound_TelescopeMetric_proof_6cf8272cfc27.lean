-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_TelescopeMetric_proof_6cf8272cfc27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:20.485539+00:00
-- url     : https://prove2.me/submissions/47eab622-5144-4e2d-98d1-bb6ec7116ef0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PTelescopeMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_TelescopeMetric_le_first_1c77e4a9049b

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
theorem _root_.solution : TelescopeMetric.Statement := by
  intro n A A' I h
  have hsum : ∑ i ∈ Finset.range (n + 1), I i ≤ (n + 1) * I 0 := by
    have := Finset.sum_le_sum (s := Finset.range (n + 1)) (f := I) (g := fun _ => I 0)
      (fun i hi => TelescopeMetric.le_first h.antitone i (by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hi))
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have := h.sum_eq
  linarith
end TelescopeMetric
end GroundTheory.Heights₂.Heights.LowerBound

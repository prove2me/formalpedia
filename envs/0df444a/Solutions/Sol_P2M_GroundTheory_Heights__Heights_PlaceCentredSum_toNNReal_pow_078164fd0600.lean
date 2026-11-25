-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_toNNReal_pow_078164fd0600
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:04.898367+00:00
-- url     : https://prove2.me/submissions/a3db4cb8-50ed-461c-8606-f3f1f1b7bd4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum

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
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
namespace GroundTheory.Heights₂.Heights.PlaceCentredSum
theorem _root_.solution {b c : NNReal} (hc : c ≠ 0) (hb : b ≠ 0) {f : ℕ} (hf : f ≠ 0) (h : c = b ^ f)
    (z : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal hc z = WithZeroMulInt.toNNReal hb z ^ f := by
  subst h
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hf]
  · rw [WithZeroMulInt.toNNReal_neg_apply _ hz, WithZeroMulInt.toNNReal_neg_apply _ hz,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
end GroundTheory.Heights₂.Heights.PlaceCentredSum

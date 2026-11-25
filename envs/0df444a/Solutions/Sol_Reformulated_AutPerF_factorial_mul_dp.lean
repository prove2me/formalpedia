-- Prove2me | solution 1 for Reformulated.AutPerF.factorial_mul_dp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:49.110656+00:00
-- url     : https://prove2.me/submissions/5d2e61c0-b1b4-46f2-9c2c-8dc3cd071f4e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {B : Type*} [CommRing B] [Algebra ℚ B]
namespace Reformulated.AutPerF
theorem _root_.solution (m : ℕ) (x : B) : (m ! : B) * dp m x = x ^ m := by
  have hm : (m ! : ℚ) ≠ 0 := by positivity
  rw [dp, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hm, one_smul]
end Reformulated.AutPerF

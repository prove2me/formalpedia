-- Prove2me | solution 1 for Reformulated.AutPerF.dp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:31:29.970861+00:00
-- url     : https://prove2.me/submissions/8f51faae-f42f-4b14-83bf-84879912b454

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
theorem _root_.solution (m : ℕ) (a x : B) : dp m (a * x) = a ^ m * dp m x := by
  rw [dp, dp, mul_pow, mul_smul_comm]
end Reformulated.AutPerF

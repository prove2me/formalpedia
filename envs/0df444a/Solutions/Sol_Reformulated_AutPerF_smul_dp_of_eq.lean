-- Prove2me | solution 1 for Reformulated.AutPerF.smul_dp_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:43.272361+00:00
-- url     : https://prove2.me/submissions/18e48a51-e6eb-46a5-b464-85a7c630dc4c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_mul_dp

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
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}
namespace Reformulated.AutPerF
theorem _root_.solution (m : ℕ) (c : A) : (ξ * c) • dp m (algebraMap A B ξ) =
    ((m + 1 : ℕ) : B) * (c • dp (m + 1) (algebraMap A B ξ)) := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_left_comm, ← mul_dp]; ring
end Reformulated.AutPerF

-- Prove2me | solution 1 for Reformulated.AutPerF.pow_dvd_dp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:56.946886+00:00
-- url     : https://prove2.me/submissions/8179763c-0f42-4f41-a429-01cf63ffabce

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
theorem _root_.solution {n m : ℕ} (h : n ≤ m) (x : B) : x ^ n ∣ dp m x := by
  rw [dp, Algebra.smul_def]
  exact (pow_dvd_pow x h).mul_left _
end Reformulated.AutPerF

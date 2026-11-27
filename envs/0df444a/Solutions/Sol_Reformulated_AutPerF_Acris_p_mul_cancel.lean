-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.p_mul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:08.511444+00:00
-- url     : https://prove2.me/submissions/2c60166a-d050-44fc-a07e-8fadd9aaaba6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero

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
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Acris
namespace Reformulated.AutPerF.Acris
theorem _root_.solution {x y : Acris p R} (h : (p : Acris p R) * x = p * y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_p_mul_eq_zero (by rw [mul_sub, h, sub_self]))
end Reformulated.AutPerF.Acris

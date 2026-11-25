-- Prove2me | solution 1 for Reformulated.AutPerF.mem_span_natCast_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:53:10.4566+00:00
-- url     : https://prove2.me/submissions/f1145ee9-de55-41d3-b4ac-3254adb4e920

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
variable {A Q : Type*} [CommRing A] [CommRing Q]
namespace Reformulated.AutPerF
theorem _root_.solution {D : Type*} [CommRing D] (p n : ℕ) (x : D) :
    x ∈ (span {(p : D)} ^ n • ⊤ : Submodule D D) ↔ (p : D) ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
end Reformulated.AutPerF

-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.theta_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:39.746394+00:00
-- url     : https://prove2.me/submissions/c7914fc8-ed72-482d-8ca6-d1e686af0d1e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_ker_theta

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
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) (x : Ainf p R) : theta p R x = 0 ↔ xi ϖ ∣ x := by
  rw [← mem_span_singleton, ← ker_theta, RingHom.mem_ker]
end Reformulated.AutPerF.Ainf

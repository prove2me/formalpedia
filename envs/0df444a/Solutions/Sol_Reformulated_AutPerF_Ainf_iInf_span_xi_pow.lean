-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.iInf_span_xi_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:23.252094+00:00
-- url     : https://prove2.me/submissions/e5293f16-8f0f-44ce-9945-4773ac807b10

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_eq_zero_of_forall_xi_pow_dvd

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
theorem _root_.solution (ϖ : PFlat p R) : ⨅ n : ℕ, span {xi ϖ} ^ n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  refine eq_zero_of_forall_xi_pow_dvd ϖ fun n => ?_
  have := Ideal.mem_iInf.1 hx n
  rwa [Ideal.span_singleton_pow, mem_span_singleton] at this
end Reformulated.AutPerF.Ainf

-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.mem_span_xi_pow_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:48.892955+00:00
-- url     : https://prove2.me/submissions/503b633b-8f43-470b-aa1b-0ab1dac150be

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_pow_dvd_of_forall

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
theorem _root_.solution (ϖ : PFlat p R) {n : ℕ} {x : Ainf p R}
    (h : ∀ k : ℕ, x ∈ span {(p : Ainf p R)} ^ k ⊔ span {xi ϖ} ^ n) : x ∈ span {xi ϖ} ^ n := by
  rw [Ideal.span_singleton_pow, mem_span_singleton]
  refine xi_pow_dvd_of_forall ϖ fun k => ?_
  have := h k
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, ← Ideal.span_insert,
    Ideal.mem_span_pair] at this
  obtain ⟨a, b, e⟩ := this
  exact ⟨a, b, by linear_combination -e⟩
end Reformulated.AutPerF.Ainf

-- Prove2me | solution 1 for PI.WAU.B.exists_nat_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:06.683651+00:00
-- url     : https://prove2.me/submissions/48a4a32f-d1a7-4b61-9cca-7f28f2e01556

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU.B
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hxb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  have hN : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero hN, ?_⟩
  have key : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : v.adicCompletion F) =
      (c : v.adicCompletion F) * (b : v.adicCompletion F) := by
    have h3 := congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc.symm
    rw [map_natCast, map_mul] at h3
    exact h3
  rw [key, mul_assoc, mul_comm (b : v.adicCompletion F) x]
  exact mul_mem (coe_mem_adicCompletionIntegers v c) hxb
end PI.WAU.B

-- Prove2me | solution 1 for PI.AdCpctDenWork.exists_nat_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:44.651522+00:00
-- url     : https://prove2.me/submissions/add029f6-e57b-4231-a0e3-c191904a550e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AdCpctDenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.AdCpctDenWork
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  · have h1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : v.adicCompletion F)
        = algebraMap (𝓞 F) (v.adicCompletion F) c * algebraMap (𝓞 F) (v.adicCompletion F) b := by
      rw [← map_mul, hc, map_natCast]
    rw [h1, mul_assoc, mul_comm (algebraMap _ _ b) x]
    exact mul_mem (coe_mem_adicCompletionIntegers v c) hbx
end PI.AdCpctDenWork

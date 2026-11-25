-- Prove2me | solution 1 for PI.OkpW.exists_inv_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:16.225115+00:00
-- url     : https://prove2.me/submissions/4bdfe46d-2e86-4ad4-9d02-4458e8c755dc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
import Theorems.Thm_PI_OkpW_isMaximal_span_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
namespace PI.OkpW
theorem _root_.solution (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K} (ha : ¬ (p : 𝓞 K) ∣ a) :
    ∃ b : 𝓞 K, (p : 𝓞 K) ∣ a * b - 1 := by
  have hM : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI := Ideal.Quotient.field (Ideal.span {(p : 𝓞 K)})
  have h0 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) a)⁻¹
  refine ⟨b, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_mul, hb, map_one, mul_inv_cancel₀ h0]
end PI.OkpW

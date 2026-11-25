-- Prove2me | solution 1 for PI.OkpW.pow_q_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:21.475103+00:00
-- url     : https://prove2.me/submissions/4ef247ef-586c-49b8-8dde-06a7ae18f36b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
import Theorems.Thm_PI_OkpW_isMaximal_span_p
import Theorems.Thm_PI_OkpW_natCard_quot
import Theorems.Thm_PI_OkpW_finite_quot

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
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime)
    (a : 𝓞 K) (n : ℕ) : (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have hM : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI := Ideal.Quotient.field (Ideal.span {(p : 𝓞 K)})
  haveI := finite_quot (K := K) (p := p) hK
  letI := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})
  have hc : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, natCard_quot hK]
  rw [map_pow, ← hc, FiniteField.pow_card_pow]
end PI.OkpW

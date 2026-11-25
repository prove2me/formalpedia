-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.exists_not_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:19.807209+00:00
-- url     : https://prove2.me/submissions/647d5fb2-865d-46f6-94ad-58fb70b1fa23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_mem_pow_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open PI.TwistedEisensteinNonvanishing.W.NTA
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwistedEisensteinNonvanishing.W.NTA
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} (hα : α ≠ 0) :
    ∃ K : ℕ, ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ K, α ∈ P.asIdeal ^ K := fun K => mem_pow_of P hp (hcon K)
  have hbot := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top
  have hin : α ∈ (⨅ i, P.asIdeal ^ i) := Ideal.mem_iInf.mpr hall
  rw [hbot, Ideal.mem_bot] at hin
  exact hα hin
end PI.TwistedEisensteinNonvanishing.W.NTA

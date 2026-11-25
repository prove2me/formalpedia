-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.mem_pow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:15.946955+00:00
-- url     : https://prove2.me/submissions/b0f259ee-d360-4014-bf97-711629fd3781

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_qO_mem
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne

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
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} {K : ℕ}
    (h : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K)) : α ∈ P.asIdeal ^ K := by
  haveI := P.isPrime
  obtain ⟨r, s, hs, h⟩ := h
  have hq0 := q_ne P hp
  have e : algebraMap (𝓞 E) E (s * α) = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E) ^ K) := by
    rw [map_mul, map_mul, map_pow, map_natCast, ← h]
    field_simp
  have hsα : s * α ∈ P.asIdeal ^ K := by
    rw [IsFractionRing.injective (𝓞 E) E e]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (qO_mem P) K)
  exact (Ideal.IsPrime.mul_mem_pow P.asIdeal hsα).resolve_left hs
end PI.TwistedEisensteinNonvanishing.W.NTA

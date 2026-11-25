-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.approx1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:45:31.475826+00:00
-- url     : https://prove2.me/submissions/5e79396a-322f-440d-b87c-a84580352460

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_qO_mem
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_res_surj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
namespace NTA
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
private theorem intAt_div_qOf_of_mem (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {α : 𝓞 E} (hα : α ∈ P.asIdeal) :
    IntAt P (algebraMap (𝓞 E) E α / (qOf P : E)) := by
  have hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (qO_mem P)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq
    have h2 : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : α * t ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hα htJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hq0 := q_ne P hp
  refine ⟨c, t, htP, ?_⟩
  have e := congrArg (algebraMap (𝓞 E) E) hc
  simp only [map_mul, map_natCast] at e
  rw [mul_div_assoc', div_eq_iff hq0]
  unfold qOf
  linear_combination -e
end NTA
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open PI.TwistedEisensteinNonvanishing.W.NTA
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwistedEisensteinNonvanishing.W.NTA
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {y : E} (hy : IntAt P y) : ∃ d : ℕ, d < qOf P ∧ IntAt P ((y - d) / (qOf P : E)) := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, hy'⟩ := hy
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨d, hdq, hd⟩ :=
    res_surj P hp (Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹)
  have hmem : r - (d : 𝓞 E) * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, mul_assoc, inv_mul_cancel₀ hs0,
      mul_one, sub_self]
  obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hmem
  have hs' : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h
    apply hs
    rw [IsFractionRing.injective (𝓞 E) E (h.trans (map_zero _).symm)]
    exact P.asIdeal.zero_mem
  have hq0 := q_ne P hp
  refine ⟨d, hdq, c, t * s, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [ht h, hs h]
  · have hy2 : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s := by
      rw [eq_div_iff hs', mul_comm]
      exact hy'
    rw [← hct, hy2, map_mul, map_sub, map_mul, map_natCast]
    field_simp
end PI.TwistedEisensteinNonvanishing.W.NTA

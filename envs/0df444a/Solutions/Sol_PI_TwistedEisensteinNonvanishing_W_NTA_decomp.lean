-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.NTA.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:38.83689+00:00
-- url     : https://prove2.me/submissions/de66721f-1bb8-4efc-908f-ef9d5245173e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iAlg
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_qO_mem
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_q_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_exists_not_int
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
    {α : 𝓞 E} (hα : α ≠ 0) : ∃ (k : ℕ) (u : E), algebraMap (𝓞 E) E α = (qOf P : E) ^ k * u ∧ u ≠ 0 ∧
      IntAt P u ∧ IntAt P u⁻¹ := by
  classical
  have hex := exists_not_int P hp hα
  have hK : ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ Nat.find hex) := Nat.find_spec hex
  have hK0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hK
    rw [h0, pow_zero, div_one]
    exact iAlg P α
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hint : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ k) :=
    not_not.mp (Nat.find_min hex (by omega : k < Nat.find hex))
  rw [hk] at hK
  have hq0 := q_ne P hp
  have hα' : algebraMap (𝓞 E) E α ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hα
  have hu0 : algebraMap (𝓞 E) E α / (qOf P : E) ^ k ≠ 0 := div_ne_zero hα' (pow_ne_zero _ hq0)
  refine ⟨k, algebraMap (𝓞 E) E α / (qOf P : E) ^ k, ?_, hu0, hint, ?_⟩
  · field_simp
  · obtain ⟨r, s, hs, hrs⟩ := hint
    have hrP : r ∉ P.asIdeal := by
      intro hr
      apply hK
      obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hr
      refine ⟨c, t * s, fun h => ?_, ?_⟩
      · rcases P.isPrime.mem_or_mem h with h | h
        exacts [ht h, hs h]
      · rw [← hct, ← hrs, map_mul]
        field_simp
        ring
    refine ⟨s, r, hrP, ?_⟩
    rw [← hrs, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
end PI.TwistedEisensteinNonvanishing.W.NTA

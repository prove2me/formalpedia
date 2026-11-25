-- Prove2me | solution 1 for PI.TwNormLat.W.unit_of_not_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:28.991806+00:00
-- url     : https://prove2.me/submissions/526246ed-4a5a-4ec7-9964-ab1d275b59fa

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Theorems.Thm_P2M_PI_TwNormLat_W_mul_notMem__ff4d1c9ef9d9
import Theorems.Thm_PI_TwNormLat_W_qE_ne_zero
import Theorems.Thm_PI_TwNormLat_W_uniform_continuity_galois_group

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
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {y : E} (hy : IntAt P y)
    (hy' : ¬ IntAt P (y / qE P)) : IntAt P y⁻¹ := by
  obtain ⟨r, s, hs, h⟩ := hy
  by_cases hr : r ∈ P.asIdeal
  · exfalso
    obtain ⟨s', t, hs', ht⟩ := PI.TwNormLat.W.uniform_continuity_galois_group P hq hr
    apply hy'
    refine ⟨t, s * s', PI.TwNormLat.W.mul_notMem' P hs hs', ?_⟩
    have hq0 := PI.TwNormLat.W.qE_ne_zero P hp
    have ht' : algebraMap (𝓞 E) E t * qE P = algebraMap (𝓞 E) E s' * algebraMap (𝓞 E) E r := by
      have e := congrArg (algebraMap (𝓞 E) E) ht
      simpa using e
    rw [map_mul, mul_div_assoc', div_eq_iff hq0, ht', ← h]
    ring
  · refine ⟨s, r, hr, ?_⟩
    have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
      intro h0
      apply hr
      have hr' : r = 0 := IsFractionRing.injective (𝓞 E) E (by rw [h0, map_zero])
      rw [hr']
      exact P.asIdeal.zero_mem
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hr0
      rw [← h, mul_zero]
    rw [← h, mul_assoc, mul_inv_cancel₀ hy0, mul_one]
end PI.TwNormLat.W

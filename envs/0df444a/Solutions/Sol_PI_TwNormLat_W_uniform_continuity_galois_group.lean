-- Prove2me | solution 1 for PI.TwNormLat.W.uniform_continuity_galois_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:55.632636+00:00
-- url     : https://prove2.me/submissions/07598bc7-2dea-4055-9e7f-e33104cd236f

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup

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
theorem _root_.solution (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r : 𝓞 E} (hr : r ∈ P.asIdeal) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ t * ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) = s * r := by
  have hqP : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr hqP
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hJ'
    apply hq
    have hsq : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hJ'
    exact hsq (Ideal.mem_span_singleton_self _)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : s * r ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} := by
    rw [hJ, mul_comm s r]
    exact Ideal.mul_mem_mul hr hsJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨s, t, hsP, ht⟩
end PI.TwNormLat.W

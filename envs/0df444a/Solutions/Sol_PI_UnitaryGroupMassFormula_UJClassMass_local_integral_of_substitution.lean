-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.local_integral_of_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:31.010194+00:00
-- url     : https://prove2.me/submissions/55774aa2-de78-444f-ad3a-5447009c489d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LocalIntegralOfSubstitution
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : LocInt := by
  intro F _ _ t z c u hu hz
  by_cases hc : (c : F) = 0
  · refine ⟨1, t.asIdeal.primeCompl.one_mem, 0, ?_⟩
    rw [hc, map_zero, zero_mul] at hz
    have hz0 : z = 0 := (algebraMap F (t.adicCompletion F)).injective (by rw [hz, map_zero])
    simp [hz0]
  · have hxu : algebraMap F (t.adicCompletion F) (z / (c : F)) = u := by
      rw [map_div₀, hz, mul_div_cancel_left₀ _ ((map_ne_zero _).2 hc)]
    have hu' : algebraMap F (t.adicCompletion F) (z / (c : F)) ∈ t.adicCompletionIntegers F :=
      hxu ▸ hu
    have e : ∀ x : F, Valued.v (algebraMap F (t.adicCompletion F) x) = t.valuation F x := by
      intro x
      first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation t x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation x
      | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      | rfl
    have hv : t.valuation F (z / (c : F)) ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hu'
      rw [← e]
      exact hu'
    obtain ⟨n, m, hm, hnm⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (z / (c : F))
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hvm : t.intValuation m ≠ 0 := HeightOneSpectrum.intValuation_ne_zero t m hm0
    have hnm' : t.intValuation n ≤ t.intValuation m := by
      rw [← hnm, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap] at hv
      exact (div_le_one₀ (zero_lt_iff.2 hvm)).1 hv
    have hI0 : Ideal.span {m} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hm0
    obtain ⟨k, J, hJt, hmJ⟩ := WfDvdMonoid.max_power_factor hI0 t.irreducible
    have hnk : n ∈ t.asIdeal ^ k := by
      have hdm : t.asIdeal ^ k ∣ Ideal.span {m} := ⟨J, hmJ⟩
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hdm
      have hdn := (HeightOneSpectrum.intValuation_le_pow_iff_dvd t n k).1 (hnm'.trans hdm)
      exact Ideal.dvd_span_singleton.1 hdn
    have hJ : ¬ J ≤ t.asIdeal := fun h => hJt (Ideal.dvd_iff_le.2 h)
    obtain ⟨d, hdJ, hdt⟩ := SetLike.not_le_iff_exists.1 hJ
    have hdn : d * n ∈ Ideal.span {m} := by
      rw [hmJ, mul_comm d n]
      exact Ideal.mul_mem_mul hnk hdJ
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hdn
    refine ⟨d, hdt, a, ?_⟩
    have hmF : algebraMap (𝓞 F) F m ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    have ha' : algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F m =
        algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F n := by
      rw [← map_mul, ← map_mul, ha]
    have hzm : z * algebraMap (𝓞 F) F m = (c : F) * algebraMap (𝓞 F) F n := by
      have h3 : z = (c : F) * (algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F m) := by
        rw [hnm]
        field_simp
      rw [h3, mul_assoc, div_mul_cancel₀ _ hmF]
    show z * algebraMap (𝓞 F) F d = (c : F) * algebraMap (𝓞 F) F a
    apply mul_right_cancel₀ hmF
    linear_combination (algebraMap (𝓞 F) F d) * hzm - (c : F) * ha'
end PI.UnitaryGroupMassFormula.UJClassMass

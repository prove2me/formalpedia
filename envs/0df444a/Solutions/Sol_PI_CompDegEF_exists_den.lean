-- Prove2me | solution 1 for PI.CompDegEF.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:53.961078+00:00
-- url     : https://prove2.me/submissions/9e561a9e-fc60-467c-9360-c6170d64f203

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_ExistsDen
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (v : HeightOneSpectrum (𝓞 E))
    (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal))
    (e : E) (he : ‖φ e‖ ≤ 1) :
    ∃ s a : 𝓞 E, s ∉ v.asIdeal ∧ e * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
  classical
  have hunit : ∀ s : 𝓞 E, s ∉ v.asIdeal → ‖φ (algebraMap (𝓞 E) E s)‖ = 1 :=
    fun s hs => le_antisymm (hφ s).1 (not_lt.mp fun h => hs ((hφ s).2.mp h))
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hrel : ∀ u w : 𝓞 E, a * u = d * w →
      algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E d * algebraMap (𝓞 E) E u = algebraMap (𝓞 E) E w := by
    intro u w huw
    rw [div_mul_eq_mul_div, div_eq_iff hd0, ← map_mul, ← map_mul, huw, mul_comm]
  haveI : IsDomain (Localization.AtPrime v.asIdeal) := by
    first
      | infer_instance
      | exact IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors v.asIdeal)
  haveI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := by
    first
      | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) v.ne_bot _
      | infer_instance
  haveI : ValuationRing (Localization.AtPrime v.asIdeal) := inferInstance
  have hinj := IsLocalization.injective (Localization.AtPrime v.asIdeal)
    (Ideal.primeCompl_le_nonZeroDivisors v.asIdeal)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) d)
    (algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) a)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl c
  have hs : (s : 𝓞 E) ∉ v.asIdeal := s.2
  rcases hc with h | h
  · have key : algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (d * r) =
        algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (a * s) := by
      rw [map_mul, map_mul, ← h, ← IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) r s]
      ring
    have hdr := hinj key
    exact ⟨s, r, hs, hrel s r hdr.symm⟩
  · have key : algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (a * r) =
        algebraMap (𝓞 E) (Localization.AtPrime v.asIdeal) (d * s) := by
      rw [map_mul, map_mul, ← h, ← IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) r s]
      ring
    have hdr := hinj key
    by_cases hr : r ∈ v.asIdeal
    · exfalso
      have hmul := hrel r s hdr
      have hn := congrArg (fun z => ‖φ z‖) hmul
      simp only [map_mul, norm_mul] at hn
      have h1 : ‖φ (algebraMap (𝓞 E) E r)‖ < 1 := (hφ r).2.mpr hr
      rw [hunit s hs] at hn
      have hlt : ‖φ (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E d)‖ * ‖φ (algebraMap (𝓞 E) E r)‖ < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) he) h1
      linarith
    · exact ⟨r, s, hr, hrel r s hdr⟩
end PI.CompDegEF

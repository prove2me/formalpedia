-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.condExact_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:45.867562+00:00
-- url     : https://prove2.me/submissions/f556c7c1-6778-406e-85fc-e1c738632071

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolS
import Theorems.Thm_PI_VolStabSW_VolAAW_af_sub
import Theorems.Thm_PI_VolStabSW_VolAAW_singleV_self
import Theorems.Thm_PI_VolStabSW_VolAAW_singleV_ne
import Theorems.Thm_PI_VolStabSW_VolAAW_isOpen_adelic_neighbourhood
import Theorems.Thm_PI_VolStabSW_VolAAW_adele_character_trivial_open
import Theorems.Thm_PI_VolStabSW_VolAAW_algebraMap_AF
import Theorems.Thm_PI_VolStabSW_VolAAW_psi_fin_of_char
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
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabSW.VolAAW
theorem _root_.solution (hS : SAf) (hC : ChInf) : CondExact := by
  intro F _ _ ψ hψ
  classical
  obtain ⟨I, n, hU⟩ := adele_character_trivial_open ψ hψ
  by_contra hne
  rw [Filter.not_eventually, Filter.frequently_cofinite_iff_infinite] at hne
  set X := {v : HeightOneSpectrum (𝓞 F) | ¬∀ t : Fv F v,
    (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F}
    with hX

  have key : ∀ v ∈ X, v ∉ I → ∃ a : F, 1 < Valued.v (algebraMap F (Fv F v) a) ∧ a ∈ lamPsi ψ := by
    intro v hvX hvI
    simp only [hX, Set.mem_setOf_eq, not_forall] at hvX
    obtain ⟨t, ht, htO⟩ := hvX
    have ht1 : 1 < Valued.v t := (HeightOneSpectrum.notMem_adicCompletionIntegers (𝓞 F) F v).1 htO
    obtain ⟨a, ha⟩ := hS F (U0 I n) (isOpen_adelic_neighbourhood I n) (singleV F v t)
    have hdv : (singleV F v t - algebraMap F (Af F) a) v = t - algebraMap F (Fv F v) a := by
      rw [af_sub, singleV_self]
      rfl
    have hdw : ∀ w, w ≠ v → (singleV F v t - algebraMap F (Af F) a) w = - algebraMap F (Fv F w) a := by
      intro w hw
      rw [af_sub, singleV_ne v w hw, zero_sub]
      rfl
    have hta : Valued.v (t - algebraMap F (Fv F v) a) < Valued.v t := by
      have := ha.1 v
      rw [hdv, HeightOneSpectrum.mem_adicCompletionIntegers] at this
      exact lt_of_le_of_lt this ht1
    have hav : Valued.v (algebraMap F (Fv F v) a) = Valued.v t := by
      have := Valuation.map_sub_eq_of_lt_left Valued.v hta
      rwa [sub_sub_cancel] at this
    refine ⟨a, hav ▸ ht1, ?_⟩
    intro r
    have hrint : ∀ w : HeightOneSpectrum (𝓞 F),
        algebraMap F (Fv F w) (r : F) ∈ w.adicCompletionIntegers F := by
      intro w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have e : Valued.v (((r : F) : w.adicCompletion F)) = w.valuation F (r : F) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (r : F)
      exact (e ▸ w.valuation_le_one r : Valued.v (((r : F) : w.adicCompletion F)) ≤ 1)
    set y : Af F := algebraMap F (Af F) ((r : F) * a) with hy
    have hyw : ∀ w, y w = algebraMap F (Fv F w) (r : F) * algebraMap F (Fv F w) a := by
      intro w
      rw [hy, map_mul]
      rfl
    have hz : y - singleV F v (y v) ∈ U0 I n := by
      refine ⟨fun w => ?_, fun w hw => ?_⟩
      · rw [af_sub]
        by_cases hwv : w = v
        · subst hwv
          rw [singleV_self, sub_self]
          exact zero_mem _
        · rw [singleV_ne v w hwv, sub_zero, hyw]
          refine mul_mem (hrint w) ?_
          have := neg_mem (ha.1 w)
          rwa [hdw w hwv, neg_neg] at this
      · have hwv : w ≠ v := fun h => hvI (h ▸ hw)
        rw [af_sub, singleV_ne v w hwv, sub_zero, hyw, mul_left_comm]
        refine mul_mem (hrint w) ?_
        have := neg_mem (ha.2 w hw)
        rwa [hdw w hwv, mul_neg, neg_neg] at this
    have hsplit : pairA F 0 y = pairA F 0 (y - singleV F v (y v)) + pairA F 0 (singleV F v (y v)) := by
      rw [← adele_pairing_zero_add, sub_add_cancel]
    show ψ (pairA F 0 y) = 1
    rw [hsplit, AddChar.map_add_eq_mul, hU _ hz, one_mul]
    show psiV F ψ v (y v) = 1
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht1
    have hq : y v / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hyw, map_mul, hav,
        mul_div_assoc, div_self ((Valuation.ne_zero_iff _).2 ht0), mul_one]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hrint v)
    have := ht _ hq
    rwa [div_mul_cancel₀ _ ht0] at this

  have hne' : ∀ c : F, ∃ v, v ∈ X ∧ v ∉ I ∧ v ∉ HeightOneSpectrum.Support (𝓞 F) c := by
    intro c
    obtain ⟨v, hv⟩ := ((hne.diff I.finite_toSet).diff (HeightOneSpectrum.Support.finite (𝓞 F) c)).nonempty
    exact ⟨v, hv.1.1, hv.1.2, hv.2⟩
  have h0 : ∃ c : F, c ≠ 0 ∧ c ∈ lamPsi ψ := by
    obtain ⟨v, hvX, hvI, -⟩ := hne' 1
    obtain ⟨a, ha1, ha⟩ := key v hvX hvI
    refine ⟨a, ?_, ha⟩
    rintro rfl
    simp at ha1
  have hb : ∀ c : F, c ≠ 0 → ¬ ∀ a ∈ lamPsi ψ, ∃ r : 𝓞 F, a = c * r := by
    intro c _ hall
    obtain ⟨v, hvX, hvI, hvc⟩ := hne' c
    obtain ⟨a, ha1, ha⟩ := key v hvX hvI
    obtain ⟨r, rfl⟩ := hall a ha
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hvc
    have hc : Valued.v (algebraMap F (Fv F v) c) ≤ 1 := by
      have e : Valued.v ((c : v.adicCompletion F)) = v.valuation F c :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c
      exact (e ▸ hvc : Valued.v ((c : v.adicCompletion F)) ≤ 1)
    have hr : Valued.v (algebraMap F (Fv F v) (r : F)) ≤ 1 := by
      have e : Valued.v (((r : F) : v.adicCompletion F)) = v.valuation F (r : F) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (r : F)
      exact (e ▸ v.valuation_le_one r : Valued.v (((r : F) : v.adicCompletion F)) ≤ 1)
    rw [map_mul, map_mul] at ha1
    have : Valued.v (algebraMap F (Fv F v) c) * Valued.v (algebraMap F (Fv F v) (r : F)) ≤ 1 :=
      mul_le_one' hc hr
    exact absurd ha1 (not_lt.2 this)
  have hχc : Continuous (chiInf ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  have hΛ : ∀ a ∈ lamPsi ψ, chiInf ψ (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
    intro a ha
    apply psi_fin_of_char ψ hψ a
    have := ha 1
    simpa using this
  have hall := hC F (lamPsi ψ) h0 hb (chiInf ψ) hχc hΛ
  obtain ⟨x, hx⟩ := hψ.2.2.2
  apply hx
  obtain ⟨a, ha⟩ := hS F (U0 I n) (isOpen_adelic_neighbourhood I n) x.2
  have e : x = algebraMap F (AF F) a + pairA F (x.1 - algebraMap F (Ainf F) a) 0 +
      pairA F 0 (x.2 - algebraMap F (Af F) a) := by
    rw [algebraMap_AF]
    refine Prod.ext ?_ ?_
    · show x.1 = algebraMap F (Ainf F) a + 0 + (x.1 - algebraMap F (Ainf F) a) + 0
      abel
    · show x.2 = 0 + algebraMap F (Af F) a + 0 + (x.2 - algebraMap F (Af F) a)
      abel
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.2.1 a, hU _ ha, one_mul, mul_one]
  exact hall _
end PI.VolStabSW.VolAAW

-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.t_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:06.68305+00:00
-- url     : https://prove2.me/submissions/b4fde50f-5c19-4d99-8f95-24add01a9ad6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finElt
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_one_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_sub_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_apply
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
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (m : 𝓞 F) (hm : m ≠ 0) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      (1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) ∈ intAf F := by
  classical
  have hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ n : ℕ, m ∉ w.asIdeal ^ n := by
    intro w
    by_contra h
    push_neg at h
    have hmem : m ∈ ⨅ i, w.asIdeal ^ i := (Submodule.mem_iInf _).2 h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top, Ideal.mem_bot] at hmem
    exact hm hmem
  choose n hn using hn
  let s : Finset (HeightOneSpectrum (𝓞 F)) := insert v (finElt m hm).toFinset
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun w => w.asIdeal)
    (fun w => if w = v then 1 else n w) (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then 1 else 0)
  refine ⟨t, ?_, ?_⟩
  · intro htv
    have h1 : t - 1 ∈ v.asIdeal := by simpa using ht v (Finset.mem_insert_self _ _)
    have h2 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem htv h1
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · intro w
    show ((1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m)) w ∈
      w.adicCompletionIntegers F
    rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
    split_ifs with hw
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) =
          ((algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m : F) : w.adicCompletion F) := rfl
      rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_div₀,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hw' : w ≠ v := fun h => hw (by rw [h]; exact Set.mem_singleton v)
      have hpos : 0 < w.intValuation m := zero_lt_iff.2 (HeightOneSpectrum.intValuation_ne_zero w m hm)
      by_cases hmw : m ∈ w.asIdeal
      · have hws : w ∈ s := Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hmw)
        have h1 := ht w hws
        simp only [if_neg hw', sub_zero] at h1
        have hle := (HeightOneSpectrum.intValuation_le_pow_iff_mem w t (n w)).2 h1
        have hnot : ¬ w.intValuation m ≤ WithZero.exp (-((n w : ℕ) : ℤ)) :=
          fun h => hn w ((HeightOneSpectrum.intValuation_le_pow_iff_mem w m (n w)).1 h)
        have hlt := lt_of_le_of_lt hle (not_le.1 hnot)
        exact (div_le_one₀ hpos).2 hlt.le
      · rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w m).2 hmw, div_one]
        exact HeightOneSpectrum.intValuation_le_one w t
end PI.UnitaryGroupMassFormula.UJClassMass

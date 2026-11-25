-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.testEx_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:46.821532+00:00
-- url     : https://prove2.me/submissions/1b7dafb2-ce5a-4d64-8e04-3f4daf570e91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution (hχ : ∀ x y, χ x y = 1) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) : TestEx μ χ := by
  classical
  have hLcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  by_cases hL : ∀ t, t ∈ L
  · have hu : (Set.univ : Set V) = L := (Set.eq_univ_of_forall (s := (L : Set V)) hL).symm
    haveI : IsFiniteMeasure μ := ⟨by rw [hu]; exact hLc.measure_lt_top⟩
    refine ⟨fun _ => 1, continuous_const, HasCompactSupport.intro hLc fun x hx => absurd (hL x) hx,
      ?_, 0, one_ne_zero⟩
    simp_rw [hχ, mul_one]
    exact integrable_const _
  · push_neg at hL
    obtain ⟨t, ht⟩ := hL
    set S : Set V := (fun x => -t + x) ⁻¹' (L : Set V) with hS
    have hScl : IsClopen S := hLcl.preimage (continuous_const.add continuous_id)
    have hSc : IsCompact S := (Homeomorph.addLeft (-t)).isCompact_preimage.2 hLc
    have hSμ : μ S = μ (L : Set V) := measure_preimage_add μ (-t) (L : Set V)
    have hiL : Integrable ((L : Set V).indicator fun _ => (1 : ℂ)) μ :=
      (integrable_indicator_iff hLo.measurableSet).2 (continuousOn_const.integrableOn_compact hLc)
    have hiS : Integrable (S.indicator fun _ => (1 : ℂ)) μ :=
      (integrable_indicator_iff hScl.isOpen.measurableSet).2 (continuousOn_const.integrableOn_compact hSc)
    refine ⟨fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x - S.indicator (fun _ => (1 : ℂ)) x,
      ?_, ?_, ?_, 0, ?_⟩
    · exact (hLcl.continuous_indicator continuous_const).sub (hScl.continuous_indicator continuous_const)
    · refine HasCompactSupport.intro (hLc.union hSc) fun x hx => ?_
      simp only [Set.mem_union, not_or] at hx
      simp [Set.indicator, hx.1, hx.2]
    · have h0 : (fun y => ∫ x, ((L : Set V).indicator (fun _ => (1 : ℂ)) x -
          S.indicator (fun _ => (1 : ℂ)) x) * χ x y ∂μ) = fun _ => 0 := by
        funext y
        simp_rw [hχ, mul_one]
        rw [integral_sub hiL hiS, integral_indicator_const _ hLo.measurableSet,
          integral_indicator_const _ hScl.isOpen.measurableSet]
        simp [Measure.real, hSμ]
      rw [h0]
      exact integrable_zero _ _ _
    · simp [Set.indicator, hS, ht]
end PI.VolStabSW.SdUniqW

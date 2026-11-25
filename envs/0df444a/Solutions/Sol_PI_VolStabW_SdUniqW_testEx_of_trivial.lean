-- Prove2me | solution 1 for PI.VolStabW.SdUniqW.testEx_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:25.591794+00:00
-- url     : https://prove2.me/submissions/fe59fb8f-b410-4654-9e05-d7509be48809

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
namespace PI.VolStabW.SdUniqW
theorem _root_.solution (hχ : ∀ x y, χ x y = 1) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) : TestEx μ χ := by
  classical
  set g : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hg
  have gc : Continuous g :=
    IsClopen.continuous_indicator ⟨L.isClosed_of_isOpen hLo, hLo⟩ continuous_const
  have gs : HasCompactSupport g := HasCompactSupport.intro hLc (fun x hx => by simp [hg, hx])
  by_cases hall : ∀ t, t ∈ L
  · refine ⟨g, gc, gs, ?_, ⟨0, by simp [hg]⟩⟩
    have huniv : (L : Set V) = Set.univ := Set.eq_univ_of_forall hall
    haveI : CompactSpace V := ⟨huniv ▸ hLc⟩
    simp only [hχ, mul_one]
    exact integrable_const _
  · push_neg at hall
    obtain ⟨t, ht⟩ := hall
    have gc' : Continuous (fun x => g (x - t)) := gc.comp (continuous_sub_right t)
    have gs' : HasCompactSupport (fun x => g (x - t)) :=
      gs.comp_homeomorph (Homeomorph.subRight t)
    refine ⟨fun x => g x - g (x - t), gc.sub gc', gs.sub gs', ?_, ⟨0, ?_⟩⟩
    · have h0 : ∀ y, ∫ x, (g x - g (x - t)) * χ x y ∂μ = 0 := by
        intro y
        simp only [hχ, mul_one]
        rw [integral_sub (gc.integrable_of_hasCompactSupport gs)
          (gc'.integrable_of_hasCompactSupport gs'), integral_sub_right_eq_self, sub_self]
      simp only [h0]
      exact integrable_zero _ _ _
    · simp [hg, ht]
end PI.VolStabW.SdUniqW

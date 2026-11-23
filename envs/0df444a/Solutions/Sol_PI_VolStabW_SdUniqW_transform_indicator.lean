-- Prove2me | solution 1 for PI.VolStabW.SdUniqW.transform_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:58.393454+00:00
-- url     : https://prove2.me/submissions/f52eecc3-ebaa-4420-8dd7-4f67aa191f35

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
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
include hχ
namespace PI.VolStabW.SdUniqW
theorem _root_.solution (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ L
  · rw [Set.indicator_of_mem hy]
    have hfun : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ (L : Set V)
      · rw [Set.indicator_of_mem hx, hy x hx, one_mul]
      · simp [hx]
    rw [hfun, integral_indicator_const _ hLo.measurableSet]
    simp
  · have hy' : ∃ x0 ∈ (L : Set V), χ x0 y ≠ 1 := by
      simpa [ann] using hy
    obtain ⟨x0, hx0, hne⟩ := hy'
    rw [Set.indicator_of_notMem hy]
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have hshift : ∀ x, f (x0 + x) = χ x0 y * f x := by
      intro x
      have hmem : x0 + x ∈ (L : Set V) ↔ x ∈ (L : Set V) :=
        L.add_mem_cancel_left hx0
      by_cases hx : x ∈ (L : Set V)
      · simp only [hf, Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx, hχ]
        ring
      · have hx' : x0 + x ∉ (L : Set V) := fun h => hx (hmem.1 h)
        simp [hf, hx, hx']
    have hI : ∫ x, f x ∂μ = χ x0 y * ∫ x, f x ∂μ := by
      rw [← integral_const_mul]
      simp_rw [← hshift]
      exact (integral_add_left_eq_self (fun x => f x) x0).symm
    have h1 : (1 - χ x0 y) * ∫ x, f x ∂μ = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h
end PI.VolStabW.SdUniqW

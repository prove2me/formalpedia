-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.transform_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:02.235662+00:00
-- url     : https://prove2.me/submissions/fb2f2205-b87f-47d1-a4f3-c9340ff5b9d0

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
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
include hχ
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ L
  · rw [Set.indicator_of_mem hy]
    have e : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ (L : Set V)
      · simp [Set.indicator, hx, hy x hx]
      · simp [Set.indicator, hx]
    rw [e, integral_indicator_const _ hLo.measurableSet]
    simp
  · rw [Set.indicator_apply, if_neg hy]
    simp only [ann, Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨t, ht, hty⟩ := hy
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have key : ∫ x, f x ∂μ = χ t y * ∫ x, f x ∂μ := by
      calc ∫ x, f x ∂μ = ∫ x, f (t + x) ∂μ := (integral_add_left_eq_self f t).symm
        _ = ∫ x, χ t y * f x ∂μ := by
          congr 1
          funext x
          by_cases hx : x ∈ (L : Set V)
          · have htx : t + x ∈ L := L.add_mem ht hx
            have hx' : x ∈ L := hx
            simp [hf, Set.indicator, hx', htx, hχ]
          · have htx : t + x ∉ L := fun h => hx (by simpa using L.sub_mem h ht)
            have hx' : x ∉ L := hx
            simp [hf, Set.indicator, hx', htx]
        _ = χ t y * ∫ x, f x ∂μ := integral_const_mul _ _
    have h2 : (1 - χ t y) * ∫ x, f x ∂μ = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hty
    · exact h1
end PI.VolStabSW.SdUniqW

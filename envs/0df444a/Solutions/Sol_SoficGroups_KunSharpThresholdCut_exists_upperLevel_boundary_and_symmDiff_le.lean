-- Prove2me | solution 1 for SoficGroups.KunSharpThresholdCut.exists_upperLevel_boundary_and_symmDiff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/f005c401-2010-4b3b-8263-4e408293b7da

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_highCrossingProfile_eq_boundary
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_integrableOn_highCrossingProfile
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_setIntegral_highCrossingProfile_le_variation
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_card_symmDiff_upperLevel_le_nine_sq_error

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
namespace SoficGroups.KunSharpThresholdCut
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ) :
    ∃ t ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
      (SoficGroups.boundary σ (upperLevel f t) : ℝ) ≤
          3 * ∑ i : ι,
            ∑ x ∈ Finset.univ.filter
              (fun x : V => (1 / 3 : ℝ) < f x),
                |f (σ i x) - f x| ∧
        (((upperLevel f t ∆ T).card : ℝ)) ≤
          9 * ∑ x : V,
            (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
  have hpos : volume (Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) ≠ 0 := by
    norm_num [Real.volume_Ioo]
  have hfin : volume (Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) ≠ ∞ := by
    simp [Real.volume_Ioo]
  obtain ⟨t, ht, hmean⟩ :=
    exists_le_setAverage (μ := volume)
      (s := Ioo (1 / 3 : ℝ) (2 / 3 : ℝ))
      hpos hfin
      (integrableOn_highCrossingProfile σ f (1 / 3) _ _)
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← highCrossingProfile_eq_boundary σ f (1 / 3) t ht.1]
    calc
      highCrossingProfile σ f (1 / 3) t ≤
          ⨍ u in Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
            highCrossingProfile σ f (1 / 3) u := hmean
      _ = 3 * (∫ u in Ioo (1 / 3 : ℝ) (2 / 3 : ℝ),
            highCrossingProfile σ f (1 / 3) u) := by
        rw [setAverage_eq, Real.volume_real_Ioo]
        norm_num
      _ ≤ 3 * ∑ i : ι,
          ∑ x ∈ Finset.univ.filter
            (fun x : V => (1 / 3 : ℝ) < f x),
              |f (σ i x) - f x| :=
        mul_le_mul_of_nonneg_left
          (setIntegral_highCrossingProfile_le_variation
            σ f (1 / 3) (1 / 3) (2 / 3)) (by norm_num)
  · exact card_symmDiff_upperLevel_le_nine_sq_error
      T f t ht.1.le ht.2.le
end SoficGroups.KunSharpThresholdCut

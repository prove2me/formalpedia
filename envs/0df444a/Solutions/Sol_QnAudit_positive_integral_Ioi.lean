-- Prove2me | solution 1 for QnAudit.positive_integral_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:54:15.841722+00:00
-- url     : https://prove2.me/submissions/9b4bc3a7-6aaa-400e-a1eb-95dd6c87b452

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem solution (f : ℝ → ℝ)
    (hf : ∀ t > 0, 0 < f t)
    (hi : IntegrableOn f (Ioi 0)) :
    0 < ∫ t in Ioi (0 : ℝ), f t := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact le_of_lt (hf t ht)
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg hi).2
  have hsub : Ioc (0 : ℝ) 1 ⊆ Function.support f := by
    intro t ht
    exact ne_of_gt (hf t ht.1)
  have hmeasure : (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 1) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    have hinter : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 :=
      inter_eq_left.mpr (fun _ ht => ht.1)
    rw [hinter, Real.volume_Ioc]
    norm_num
  calc
    0 < (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 1) := by rw [hmeasure]; norm_num
    _ ≤ (volume.restrict (Ioi (0 : ℝ))) (Function.support f) := measure_mono hsub

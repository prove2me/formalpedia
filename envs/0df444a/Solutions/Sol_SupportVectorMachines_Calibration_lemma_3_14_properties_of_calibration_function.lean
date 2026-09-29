-- Prove2me | solution 1 for SupportVectorMachines.Calibration.lemma_3_14_properties_of_calibration_function
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:18:06.021267+00:00
-- url     : https://prove2.me/submissions/32455d08-6f2b-4101-80d8-2c8ea97f825a

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction

open MeasureTheory

namespace SupportVectorMachines.Calibration

theorem aux_l314_le_inner {X : Type*} (L : Loss X) (Q : Measure ℝ) (x : X) (t : ℝ) :
    minInnerRisk L Q x ≤ innerRisk L Q x t := iInf_le _ t

theorem aux_l314_min_le_inf {X : Type*} (Ltar Lsur : Loss X) (Q : Measure ℝ) (x : X)
    (ε : ENNReal) :
    minInnerRisk Lsur Q x ≤
      ⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Ltar Q x ε}, innerRisk Lsur Q x t :=
  le_iInf₂ fun t _ => iInf_le _ t

end SupportVectorMachines.Calibration

open MeasureTheory
open SupportVectorMachines.Calibration

theorem solution {X : Type*} (Ltar Lsur : Loss X)
    (Q : Measure ℝ) (x : X) (ε : ENNReal) :
    (approxMinimizers Lsur Q x (calibrationFunction Ltar Lsur Q x ε) ⊆
        approxMinimizers Ltar Q x ε) ∧
    (∀ δ : ENNReal, calibrationFunction Ltar Lsur Q x ε < δ →
      ¬ (approxMinimizers Lsur Q x δ ⊆ approxMinimizers Ltar Q x ε)) ∧
    (minInnerRisk Ltar Q x < ⊤ → minInnerRisk Lsur Q x < ⊤ →
      ∀ t : ℝ, calibrationFunction Ltar Lsur Q x
          (innerRisk Ltar Q x t - minInnerRisk Ltar Q x) ≤
        innerRisk Lsur Q x t - minInnerRisk Lsur Q x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [approxMinimizers, Set.mem_ofPred_eq] at ht
    unfold calibrationFunction at ht
    split_ifs at ht with h
    · exfalso
      have hle := aux_l314_le_inner Lsur Q x t
      rw [h] at hle
      rw [top_le_iff.mp hle, h] at ht
      simp at ht
    · rw [add_tsub_cancel_of_le (aux_l314_min_le_inf Ltar Lsur Q x ε)] at ht
      by_contra hn
      exact absurd (iInf₂_le t hn) (not_le.mpr ht)
  · intro δ hδ hsub
    unfold calibrationFunction at hδ
    split_ifs at hδ with h
    · exact not_top_lt hδ
    · have hle := aux_l314_min_le_inf Ltar Lsur Q x ε
      rw [ENNReal.sub_lt_iff_lt_right h hle, add_comm] at hδ
      rw [iInf_lt_iff] at hδ
      obtain ⟨t, ht⟩ := hδ
      rw [iInf_lt_iff] at ht
      obtain ⟨hnot, hlt⟩ := ht
      exact hnot (hsub hlt)
  · intro _ hs t
    unfold calibrationFunction
    rw [if_neg hs.ne]
    apply tsub_le_tsub_right
    apply iInf₂_le t
    simp only [Set.mem_ofPred_eq, approxMinimizers,
      add_tsub_cancel_of_le (aux_l314_le_inner Ltar Q x t), lt_irrefl, not_false_eq_true]

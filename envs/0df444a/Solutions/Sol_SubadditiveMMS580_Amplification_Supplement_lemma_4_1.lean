-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.Supplement.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:08:29.094924+00:00
-- url     : https://prove2.me/submissions/cf9bd76e-f11f-4b7f-926f-e46af48983ab

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive
open SubadditiveMMS580.Amplification.Supplement

theorem solution {m : ℕ} (q : ℕ) (hq : 2 ≤ q) (v : Finset (Fin m) → ℝ)
    (hv : IsQPartitioning q v) :
    (∀ R : Finset (Fin m), IsQPartitioningOn q R v) ∧
    (∀ c : ℝ, 0 ≤ c → IsQPartitioning q (fun S => c * v S)) ∧
    (∀ C : ℝ, 0 ≤ C → IsQPartitioning q (capped v C)) := by
  obtain ⟨h0, hmono, hprice⟩ := hv
  have hnn : ∀ S, 0 ≤ v S := fun S => h0 ▸ hmono ∅ S (Finset.empty_subset _) (Finset.subset_univ _)
  refine ⟨fun R => ⟨h0, fun S T hST _ => hmono S T hST (Finset.subset_univ _),
    fun S _ t ht1 ht2 C hC hd hU => hprice S (Finset.subset_univ _) t ht1 ht2 C hC hd hU⟩, ?_, ?_⟩
  · intro c hc
    refine ⟨by simp [h0], fun S T hST hT => mul_le_mul_of_nonneg_left (hmono S T hST hT) hc, ?_⟩
    intro S hS t ht1 ht2 C hC hd hU
    obtain ⟨w, hw0, hwsum, hwJ⟩ := hprice S hS t ht1 ht2 C hC hd hU
    refine ⟨fun j => c * w j, fun j => mul_nonneg hc (hw0 j), ?_, ?_⟩
    · simp only; rw [← Finset.mul_sum, hwsum]
    · intro J; simp only; rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hwJ J) hc
  · intro K hK
    refine ⟨?_, ?_, ?_⟩
    · simp [capped, h0, hK]
    · intro S T hST hT
      exact min_le_min_right _ (hmono S T hST hT)
    · intro S hS t ht1 ht2 C hC hd hU
      obtain ⟨w, hw0, hwsum, hwJ⟩ := hprice S hS t ht1 ht2 C hC hd hU
      have hsub : ∀ J : Finset (Fin t), ∑ j ∈ J, w j ≤ v S := by
        intro J; rw [← hwsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => hw0 j)
      by_cases hle : v S ≤ K
      · refine ⟨w, hw0, ?_, ?_⟩
        · simp [capped, min_eq_left hle, hwsum]
        · intro J
          simp only [capped]
          exact le_min (hwJ J) ((hsub J).trans hle)
      · push_neg at hle
        have hpos : 0 < v S := lt_of_le_of_lt hK hle
        set a := K / v S with ha
        have ha0 : 0 ≤ a := div_nonneg hK hpos.le
        have ha1 : a ≤ 1 := (div_le_one hpos).mpr hle.le
        refine ⟨fun j => a * w j, fun j => mul_nonneg ha0 (hw0 j), ?_, ?_⟩
        · simp only [capped, min_eq_right hle.le]
          rw [← Finset.mul_sum, hwsum, ha, div_mul_cancel₀ _ hpos.ne']
        · intro J
          simp only [capped]
          rw [← Finset.mul_sum]
          apply le_min
          · calc a * ∑ j ∈ J, w j ≤ a * v (J.biUnion C) := mul_le_mul_of_nonneg_left (hwJ J) ha0
              _ ≤ 1 * v (J.biUnion C) := mul_le_mul_of_nonneg_right ha1 (hnn _)
              _ = v (J.biUnion C) := one_mul _
          · calc a * ∑ j ∈ J, w j ≤ a * v S := mul_le_mul_of_nonneg_left (hsub J) ha0
              _ = K := by rw [ha, div_mul_cancel₀ _ hpos.ne']

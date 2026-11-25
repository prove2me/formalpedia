-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSumBound_proof_202457140007
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:47.684509+00:00
-- url     : https://prove2.me/submissions/ce596d4a-868c-4006-90a8-8445ef3148d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookSumBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_exists_hookShape_of_isHook_a343077746e1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace HookSumBound
theorem _root_.solution (hC : LemmaC.Statement) (hH : HookTableauCount.Statement) :
    HookSumBound.Statement := by
  intro r a k b hk hb
  have hB0 : (0 : ℚ) ≤ (Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a) := by
    positivity
  have hterm : ∀ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      |b nu| ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) *
        (numStandardTable nu : ℚ) := by
    intro nu hnu
    have hmem := (Finset.mem_filter.mp hnu).1
    have h := Finset.mem_filter.mp hmem
    have hsum : ∑ i, nu i = k := Finset.Nat.mem_antidiagonalTuple.mp h.1
    have hc := hC r a nu (fun i j hij => h.2 i j hij)
    rw [hsum] at hc
    calc |b nu| ≤ numStandardTable (fun i => a + nu i) := hb nu hmem
      _ ≤ _ := by exact_mod_cast hc
  have himg : (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) ⊆
      (range (min r k)).image (hookShape r k) := by
    intro nu hnu
    obtain ⟨hmem, hhook⟩ := Finset.mem_filter.mp hnu
    have h := Finset.mem_filter.mp hmem
    obtain ⟨l, hlr, hlk, rfl⟩ := exists_hookShape_of_isHook hk nu (fun i j hij => h.2 i j hij)
      (Finset.Nat.mem_antidiagonalTuple.mp h.1) hhook
    exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (lt_min hlr hlk), rfl⟩
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hhooks : ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
      (numStandardTable nu : ℚ) ≤ 2 ^ (k - 1) := by
    calc _ ≤ ∑ nu ∈ (range (min r k)).image (hookShape r k), (numStandardTable nu : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity
      _ ≤ ∑ l ∈ range (min r k), (numStandardTable (hookShape r k l) : ℚ) :=
          Finset.sum_image_le_of_nonneg fun _ _ => by positivity
      _ = ∑ l ∈ range (min r k), ((k - 1).choose l : ℚ) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          have hl' := lt_min_iff.mp (Finset.mem_range.mp hl)
          rw [hH r k l hl'.2 hl'.1]
      _ ≤ ∑ l ∈ range k, ((k - 1).choose l : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _))
            fun _ _ _ => by positivity
      _ = 2 ^ (k - 1) := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          rw [Nat.add_sub_cancel]
          exact_mod_cast Nat.sum_range_choose n
  calc _ ≤ ((Nat.choose (r * a + k) k : ℚ) * numStandardTable (rectangle r a)) * 2 ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hhooks hB0
    _ = _ := by ring
end HookSumBound
end GroundTheory.Heights₂.Heights.RestTerms

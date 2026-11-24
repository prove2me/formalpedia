-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchResidueCount_proof_e127775f6b62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:30.345072+00:00
-- url     : https://prove2.me/submissions/46b48e38-e44a-48dc-910f-671ef8a6bc73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchResidueCount

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
namespace SchResidueCount
theorem _root_.solution : SchResidueCount.Statement := by
  intro k l hlt hinj
  have hsplit : ∀ i, l i = l i % k + k * (if k ≤ l i then 1 else 0) := by
    intro i
    have hi := hlt i
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have himg : (univ.image fun i => l i % k) = range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [mem_image, mem_univ, true_and] at hc
      obtain ⟨i, rfl⟩ := hc
      exact mem_range.2 (Nat.mod_lt _ i.pos)
    · rw [card_image_of_injective _ hinj, card_range, card_univ, Fintype.card_fin]
  have hres : ∑ i, l i % k = k * (k - 1) / 2 := by
    rw [← sum_range_id, ← himg, sum_image (fun i _ j _ h => hinj h)]
  calc ∑ i, l i = ∑ i, (l i % k + k * (if k ≤ l i then 1 else 0)) :=
        sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i, l i % k + k * (univ.filter fun i => k ≤ l i).card := by
        rw [sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id]
    _ = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card := by
        rw [hres]
end SchResidueCount
end GroundTheory.Heights₂.Heights.RestTerms

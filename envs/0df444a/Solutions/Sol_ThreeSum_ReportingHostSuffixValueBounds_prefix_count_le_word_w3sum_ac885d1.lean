-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:51.252188+00:00
-- url     : https://prove2.me/submissions/2b23ce15-b637-4ca2-8d5b-e25b0b7f1795

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixValueBounds
import Theorems.Thm_ThreeSum_ReportingHostSuffixValueBounds_abs_value_le_card
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftSource_abs_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_left_union_card_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_querySet_card
import Theorems.Thm_ThreeSum_BlockIndexedQuery_rightSource_abs_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_right_union_card_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_suffixStage_le
import Theorems.Thm_ThreeSum_BlockRows_mem_prefixIndices
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightBlockQuery_queryValue_eq_prefixQuery
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_residual_le_suffix
attribute [local simp] ThreeSum.BlockRows.mem_prefixIndices
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixValueBounds
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix
open scoped BigOperators
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostSuffixValueBounds
theorem _root_.solution {h J k t : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word) :
    (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ≤ lim.word := by
  have hQ : ∀ i, (outputRows w.2.2 i).card = 2*h :=
    fun i => LayerCounts.mem_vertices.mp (w.2.2 i).2.property
  have hprefix : ∀ j ∈ prefixIndices J k,
      prefixRows (J := J) pre j ⊆ outputRows w.2.2 j ∧ (prefixRows (J := J) pre j).card = h := by
    intro j hj
    exact hp.2 j (mem_prefixIndices.mp hj)
  have hQc : (querySet k (outputRows w.2.2)).card = residualSize h J k := querySet_card hk _ hQ
  have hv := abs_value_le_card
    (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))
    (querySet k (outputRows w.2.2)) (suffixStage_le J (512*h) k)
    (left_union_card_le hk _ _ hQ (fun j hj => (hprefix j hj).2))
    (right_union_card_le hk _ _ hQ hprefix)
    (fun S _ => leftSource_abs_le pMod B b w.2.2 S)
    (fun S _ => rightSource_abs_le pMod shift C c w.2.2 S)
  change |queryValue pMod shift B C b c w.2.2 k (prefixRows (J := J) pre)| ≤ _ at hv
  rw [queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey,Int.abs_natCast,hQc] at hv
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
    (LightReportingSuffixBoxes.residual_le_suffix (h := h) (J := J) (k := k))
  have hmul := Nat.mul_le_mul_right
    ((2^(suffixStage J (512*h) k)*B.card)*(2^(suffixStage J (512*h) k)*C.card)) hpow
  have hm : 2^(suffixStage J (512*h) k)*
      ((2^(suffixStage J (512*h) k)*B.card)*(2^(suffixStage J (512*h) k)*C.card)) ≤
      LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
        (residualSize h J k) t B.card C.card := Nat.le_mul_of_pos_left _ (by omega)
  exact hv.trans ((Int.ofNat_le.mpr (hmul.trans hm)).trans hvalueWord)
end ThreeSum.ReportingHostSuffixValueBounds

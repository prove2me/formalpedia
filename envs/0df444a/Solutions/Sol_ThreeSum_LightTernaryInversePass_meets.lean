-- Prove2me | solution 1 for ThreeSum.LightTernaryInversePass.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:31:15.411874+00:00
-- url     : https://prove2.me/submissions/cf241660-26e3-46ca-9a6f-535a690e2c5f

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_Light_wrote_succ
import Theorems.Thm_Light_wrote_zero
import Theorems.Thm_ThreeSum_LightTernaryCell_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_inverse_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
namespace ThreeSum.LightTernaryInversePass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
private theorem abs_sub_le_sum (a b : ℤ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
end ThreeSum.LightTernaryInversePass
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInversePass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryInversePass
theorem _root_.solution {pMain pCell pSearch pValue a n powers W L keyBase src dst d U : ℕ}
    (hmain : P[pMain]? = some (body pCell)) (hcell : P[pCell]? = some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]? = some LightTernaryCell.inverseBody) (μ : ℕ → ℤ) (codes f : ℕ → ℤ) (digits : ℕ → Fin 3)
    (ix : Fin 3 → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ dst) (hsrc : src + n ≤ dst)
    (hmeta : keyBase + 4 * n ≤ dst) (hpows : powers + (W + 1) ≤ dst) (hdst : dst + n ≤ lim.space)
    (hword : ((n + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hcodes : ∀ i < n, μ (a + i) = codes i)
    (hsource : ∀ i < n, μ (src + i) = f i) (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k) (hindex : ∀ e j, j < n → ix e j < n)
    (hmd : ∀ j < n, μ (keyBase + j) = ((digits j).val : ℤ)) (hm0 : ∀ j < n, μ (keyBase + n + j) = codes (ix 0 j))
    (hm1 : ∀ j < n, μ (keyBase + 2 * n + j) = codes (ix 1 j)) (hm2 : ∀ j < n, μ (keyBase + 3 * n + j) = codes (ix 2 j))
    (hf : ∀ j < n, |f j| ≤ U) (hvalword : 4 * (U : ℤ) + 3 ≤ lim.word) (hL : L ≤ W) (hn : n < 2 ^ L)
    (hd : d + L + 2 ≤ lim.depth) :
    Meets lim P pMain d [a, n, powers, L, keyBase, src, dst] μ (time L n)
      (fun _ μ' => (∀ j < n, μ' (dst + j) = values digits ix f j) ∧ SameOutside μ μ' dst n) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ a n powers L keyBase src dst digits ix f) n (LightTernaryLookup.time L + 85) ?start ?round ?done
      ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_zero]
    change
      frame [(a : ℤ), n, powers, L, keyBase, src, dst, 0] = frame ([(a : ℤ), n, powers, L, keyBase, src, dst, 0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r, rfl⟩
    let μj := wrote μ dst (values digits ix f) j
    have hkeep : ∀ x < dst, μj x = μ x := by
      intro x hx
      exact wrote_rest (Or.inl hx)
    have hc0 : ∀ i < n, μj (a + i) = codes i := by
      intro i hi
      rw [hkeep _ (by omega), hcodes i hi]
    have hs0 : ∀ i < n, μj (src + i) = f i := by
      intro i hi
      rw [hkeep _ (by omega), hsource i hi]
    have hp0 : Powers μj powers W := by
      intro i hi
      rw [hkeep _ (by omega), hpowers i hi]
    have hdig : μj (keyBase + j) = ((digits j).val : ℤ) := by rw [hkeep _ (by omega), hmd j hj]
    have hm0j : μj (keyBase + n + j) = codes (ix 0 j) := by rw [hkeep _ (by omega), hm0 j hj]
    have hm1j : μj (keyBase + 2 * n + j) = codes (ix 1 j) := by rw [hkeep _ (by omega), hm1 j hj]
    have hm2j : μj (keyBase + 3 * n + j) = codes (ix 2 j) := by rw [hkeep _ (by omega), hm2 j hj]
    have ha0 : ((keyBase : ℤ) + (n : ℤ) + (j : ℤ)).toNat = keyBase + n + j := by
      rw [← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast]
    have ha1 : ((keyBase : ℤ) + 2 * (n : ℤ) + (j : ℤ)).toNat = keyBase + 2 * n + j := by
      rw [show (2 : ℤ) * (n : ℤ) = ((2 * n : ℕ) : ℤ) by push_cast; rfl, ← Nat.cast_add, ← Nat.cast_add,
        Int.toNat_natCast]
    have ha2 : ((keyBase : ℤ) + 3 * (n : ℤ) + (j : ℤ)).toNat = keyBase + 3 * n + j := by
      rw [show (3 : ℤ) * (n : ℤ) = ((3 * n : ℕ) : ℤ) by push_cast; rfl, ← Nat.cast_add, ← Nat.cast_add,
        Int.toNat_natCast]
    have hc :=
      LightTernaryLookup.inverse_meets (d := d + 1) hcell hsearch hvalue μj codes (digits j) (fun e => f (ix e j)) hw
        (by omega) (by omega) (by omega) hword hc0 hp0 hsorted (hindex 0 j hj) (hindex 1 j hj) (hindex 2 j hj)
        (hs0 _ (hindex 0 j hj)) (hs0 _ (hindex 1 j hj)) (hs0 _ (hindex 2 j hj)) (fun e => hf _ (hindex e j hj)) hvalword
        hL hn (by omega)
    have hv : |values digits ix f j| ≤ 4 * (U : ℤ) :=
      by
      unfold values inverseDigit
      dsimp only
      split_ifs <;> have h0 := hf _ (hindex 0 j hj) <;> have h1 := hf _ (hindex 1 j hj) <;>
        have h2 := hf _ (hindex 2 j hj)
      · omega
      · exact (abs_sub_le_sum _ _).trans (by omega)
      · have hm : |2 * f (ix 1 j)| ≤ 2 * (U : ℤ) := by
          rw [abs_mul]
          norm_num
          omega
        calc
          |f (ix 2 j) - 2 * f (ix 1 j) + f (ix 0 j)| ≤ |f (ix 2 j) - 2 * f (ix 1 j)| + |f (ix 0 j)| := abs_add_le _ _
          _ ≤ (|f (ix 2 j)| + |2 * f (ix 1 j)|) + |f (ix 0 j)| := (add_le_add (abs_sub_le_sum _ _) le_rfl)
          _ ≤ 4 * (U : ℤ) := by omega
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, μj, hdig, ha0, ha1,
              ha2, hm0j, hm1j, hm2j, LightTernaryLookup.time, LightBandLookup.searchTime, LightTernaryCell.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [μj, hdig, ha0, ha1, ha2, hm0j, hm1j, hm2j, LightTernaryLookup.time, LightBandLookup.searchTime,
                LightTernaryCell.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, μj, hdig, ha0, ha1, ha2, hm0j, hm1j, hm2j,
              LightTernaryLookup.time, LightBandLookup.searchTime, LightTernaryCell.time] <;>
            omega)
      on_goal -1 => (rintro out μ' ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ'
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + j) (values digits ix f j) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout, values,
              LightTernaryLookup.time, LightBandLookup.searchTime, LightTernaryCell.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, values, LightTernaryLookup.time, LightBandLookup.searchTime, LightTernaryCell.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, values, LightTernaryLookup.time,
              LightBandLookup.searchTime, LightTernaryCell.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, out, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_succ, μj]
  case done =>
    rintro _ _ ⟨r, rfl⟩
    refine ⟨fun j hj => wrote_done hj, ?_⟩
    intro x hx
    exact wrote_rest hx
  case bound =>
    rintro j _ hj _ ⟨r, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightTernaryInversePass

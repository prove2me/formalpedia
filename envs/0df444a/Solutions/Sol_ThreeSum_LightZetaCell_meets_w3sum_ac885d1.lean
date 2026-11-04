-- Prove2me | solution 1 for ThreeSum.LightZetaCell.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:04.241388+00:00
-- url     : https://prove2.me/submissions/634f7b15-4977-4725-b8b9-b7f38a0e5927

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a3b2d25906ae04a
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_isMask
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_lt_iff
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_subsetMask
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
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
namespace ThreeSum.LightZetaCell
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
private theorem rank_offset {L : ℕ} (S : Finset (Fin L)) :
    layerRank L S.card (subsetMask S) + layerOffset L S.card = subsetRank S := by
  simp only [subsetRank, downsetRank, (subsetMask_isMask S).2, Nat.add_comm]
end ThreeSum.LightZetaCell
set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaCell
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaCell
theorem _root_.solution {pThis pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hThis : P[pThis]? = some (body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst work U d : ℕ} (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + downsetCap L cut ≤ work) (hdst : dst + downsetCap L cut ≤ work)
    (hspace : work + tableSize L + (L + 1) ≤ lim.space) (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2 * (U : ℤ) ≤ lim.word) (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d + L + 4 ≤ lim.depth) :
    Meets lim P pThis d [L, S.card, subsetMask S, a.val, src, dst, work] μ (time L)
      (fun _ μ' => μ' (dst + subsetRank S) = Subset.zetaStep a f S ∧ KeptExcept μ μ' work (dst + subsetRank S)) :=
  by
  have hm := subsetMask_isMask S
  have hk := hm.le_width
  have hrS := subsetRank_lt hS
  have hword₀ : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ (L + 1) : ℕ) ≤ (L + 1) * 2 ^ (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ)).trans hword
  have hfS := abs_le.mp (hvalues S hS)
  have hRankSum : (layerRank L S.card (subsetMask S) : ℤ) + (layerOffset L S.card : ℤ) = (subsetRank S : ℤ) := by
    exact_mod_cast rank_offset S
  have hRankNonneg : (0 : ℤ) ≤ layerRank L S.card (subsetMask S) := Int.natCast_nonneg _
  have hOffsetNonneg : (0 : ℤ) ≤ layerOffset L S.card := Int.natCast_nonneg _
  have hcastSize : ((L : ℤ) + 1) * ((L : ℤ) + 1) = (tableSize L : ℤ) := by simp [tableSize, pow_two]
  apply Meets.of_body hThis
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (work + tableSize L : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcastSize]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcastSize] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcastSize] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hSetup := LightSubsetSetup.meets (d := d + 1) (μ := μ) C hw hspace hword₀ hm (by omega)
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
    | refine _root_.Light.Ends.callToThen (hSetup _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hSetup ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, LightMaskErase.time,
            rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, LightMaskErase.time,
            rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime] <;>
          omega)
    on_goal -1 =>
      (rintro fullRank μ₁ ⟨hFullRank, hTable, hPowers, hKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hSread : μ₁ (src + subsetRank S) = f S := (hKept _ (by omega)).trans (hread S hS)
  have hOff := LightSubsetOffset.meets (d := d + 1) hOffset μ₁ hw (by omega) hword hTable le_rfl hk
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
    | refine _root_.Light.Ends.callToThen (hOff _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hOff ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, LightMaskErase.time,
            rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, LightMaskErase.time,
            rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime] <;>
          omega)
    on_goal -1 => (rintro fullOffset μ₂ ⟨hFullOffset, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (subsetRank S : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hFullRank, hFullOffset, hRankSum,
            LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hFullRank, hFullOffset, hRankSum, LightSubsetSetup.time, LightMaskErase.time, rankTime,
              LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hFullRank, hFullOffset, hRankSum,
            LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hDel :=
    LightMaskErase.meets hErase μ₁ hw hspace hword₀ hPowers L a.val (subsetMask S) le_rfl (Nat.le_of_lt a.isLt) hm.1
      (d + 1) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hDel _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hDel ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, LightMaskErase.time,
            rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, LightMaskErase.time,
            rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime] <;>
          omega)
    on_goal -1 => (rintro erased μ₂ ⟨hErased, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine
      _root_.Light.Ends.iteIffThen ((eraseMask L a.val (subsetMask S) : ℤ) < (subsetMask S : ℤ)) (fun hbitZ => ?_)
        (fun hnotZ => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hErased, LightSubsetSetup.time,
            LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
            powTableTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hErased, LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
              rowTime, LightArray.linearTime, powTableTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hErased, LightSubsetSetup.time,
            LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
            powTableTime] <;>
          omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have ha : a ∈ S := (eraseMask_lt_iff S a).mp (by exact_mod_cast hbitZ)
    have hkpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
    have hsubCard : (S.card : ℤ) - 1 = ((S.card - 1 : ℕ) : ℤ) := by omega
    have hE : (S.erase a).card ≤ cut := (Finset.card_le_card (Finset.erase_subset _ _)).trans hS
    have hrE := subsetRank_lt hE
    have hfE := abs_le.mp (hvalues (S.erase a) hE)
    have hEread : μ₁ (src + subsetRank (S.erase a)) = f (S.erase a) := (hKept _ (by omega)).trans (hread _ hE)
    have hMask := eraseMask_isMask S a ha
    have hkE : S.card - 1 ≤ L := by omega
    have hRankE :
      (layerRank L (S.card - 1) (eraseMask L a.val (subsetMask S)) : ℤ) + (layerOffset L (S.card - 1) : ℤ) =
        (subsetRank (S.erase a) : ℤ) :=
      by
      rw [eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
      exact_mod_cast rank_offset (S.erase a)
    have hRankENonneg : (0 : ℤ) ≤ layerRank L (S.card - 1) (eraseMask L a.val (subsetMask S)) := Int.natCast_nonneg _
    have hOffsetENonneg : (0 : ℤ) ≤ layerOffset L (S.card - 1) := Int.natCast_nonneg _
    have hRankCall :=
      rank_meets C.rank μ₁ hw (by omega) hspace hword₀ hTable hPowers L (S.card - 1) (eraseMask L a.val (subsetMask S))
        le_rfl hMask (d + 1) (by omega)
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
      | refine _root_.Light.Ends.callToThen (hRankCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hRankCall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hErased, hsubCard,
              LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hErased, hsubCard, LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
                buildTime, rowTime, LightArray.linearTime, powTableTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hErased, hsubCard, LightSubsetSetup.time,
              LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
              powTableTime] <;>
            omega)
      on_goal -1 => (rintro erasedRank μ₂ ⟨hErasedRank, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₂
    have hOffCall := LightSubsetOffset.meets (d := d + 1) hOffset μ₁ hw (by omega) hword hTable le_rfl hkE
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
      | refine _root_.Light.Ends.callToThen (hOffCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hOffCall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsubCard,
              LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hsubCard, LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                rowTime, LightArray.linearTime, powTableTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsubCard, LightSubsetSetup.time,
              LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
              powTableTime] <;>
            omega)
      on_goal -1 =>
        (rintro erasedOffset μ₂ ⟨hErasedOffset, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₂
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (subsetRank (S.erase a) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hErasedRank,
              hErasedOffset, hRankE, LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
              buildTime, rowTime, LightArray.linearTime, powTableTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hErasedRank, hErasedOffset, hRankE, LightSubsetSetup.time, LightMaskErase.time, rankTime,
                LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hErasedRank, hErasedOffset, hRankE,
              LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + subsetRank S) (f S + f (S.erase a)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hSread, hEread,
              LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hSread, hEread, LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time,
                buildTime, rowTime, LightArray.linearTime, powTableTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hSread, hEread, LightSubsetSetup.time,
              LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
              powTableTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    constructor
    · simp only [Function.update_self, Subset.zetaStep, ha, ite_true]
    · intro i hi hne
      change Function.update μ₁ (dst + subsetRank S) (f S + f (S.erase a)) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi
  · have ha : a ∉ S := by
      intro ha
      exact hnotZ (by exact_mod_cast (eraseMask_lt_iff S a).mpr ha)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + subsetRank S) (f S) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hSread,
              LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hSread, LightSubsetSetup.time, LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime,
                rowTime, LightArray.linearTime, powTableTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hSread, LightSubsetSetup.time,
              LightMaskErase.time, rankTime, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
              powTableTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    constructor
    · simp only [Function.update_self, Subset.zetaStep, ha, ite_false]
    · intro i hi hne
      change Function.update μ₁ (dst + subsetRank S) (f S) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi
end ThreeSum.LightZetaCell

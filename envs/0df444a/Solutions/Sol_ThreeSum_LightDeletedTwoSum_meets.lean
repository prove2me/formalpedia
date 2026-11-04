-- Prove2me | solution 1 for ThreeSum.LightDeletedTwoSum.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:53.264978+00:00
-- url     : https://prove2.me/submissions/f09cb95f-5481-4c4b-a719-4a9e0b039f39

import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_le_one
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_hit_succ
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_le_one
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightColoredTwoSum_hit_succ
import Theorems.Thm_ThreeSum_LightColoredTwoSum_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightDeletedTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDeletedTwoSum
theorem _root_.solution
    {pMain pTwoSum pLookup pSearch badBase badN valuesBase originalN scanBase scanN targetBase targetN powers W L U d :
      ℕ}
    (sign : ℤ) (hmain : P[pMain]? = some (body pTwoSum)) (htwo : P[pTwoSum]? = some (LightColoredTwoSum.body pLookup))
    (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ) (ids : ℕ → ℕ)
    (values scan target : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hbadSpace : badBase + badN ≤ lim.space)
    (hvaluesSpace : valuesBase + originalN ≤ lim.space) (hscanSpace : scanBase + scanN ≤ lim.space)
    (htargetSpace : targetBase + targetN ≤ lim.space) (hspace : powers + (W + 1) ≤ lim.space)
    (hword : ((targetN + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hids : ∀ i < badN, ids i < originalN)
    (hreadIds : ∀ i < badN, μ (badBase + i) = (ids i : ℤ)) (hvalues : ∀ i < originalN, |values i| ≤ U)
    (hreadValues : ∀ i < originalN, μ (valuesBase + i) = values i) (hscan : ∀ i < scanN, |scan i| ≤ U)
    (hreadScan : ∀ i < scanN, μ (scanBase + i) = scan i) (hreadTarget : ∀ i < targetN, μ (targetBase + i) = target i)
    (hsign : |sign| ≤ 1) (hvalueWord : 2 * (U : ℤ) + 3 ≤ lim.word) (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i < j → j < targetN → target i < target j) (hL : L ≤ W) (htargetN : targetN < 2 ^ L)
    (hd : d + L + 3 ≤ lim.depth) :
    Meets lim P pMain d [badBase, badN, valuesBase, originalN, scanBase, scanN, targetBase, targetN, powers, L, sign] μ
      (time badN scanN L) (fun r ν => r = (flag ids values scan target targetN scanN badN sign : ℤ) ∧ ν = μ) :=
  by
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColoredTwoSum.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColoredTwoSum.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColoredTwoSum.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := badN * (LightColoredTwoSum.time scanN L + 200) + 20) (Q :=
        Inv μ badBase badN valuesBase originalN scanBase scanN targetBase targetN powers L sign ids values scan target
          badN)
        (Inv μ badBase badN valuesBase originalN scanBase scanN targetBase targetN powers L sign ids values scan target)
        badN (LightColoredTwoSum.time scanN L + 150) ?start ?round ?done ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))))
      ?after (hT := by
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
    refine ⟨0, 0, 0, ?_⟩
    simp [update_frame_setLocal]
    change
      frame [(badBase : ℤ), badN, valuesBase, originalN, scanBase, scanN, targetBase, targetN, powers, L, sign, 0, 0] =
        frame
          ([(badBase : ℤ), badN, valuesBase, originalN, scanBase, scanN, targetBase, targetN, powers, L, sign, 0, 0] ++
            [0, 0, 0])
    exact (frame_append_zeros _ 3).symm
  case round =>
    rintro j _ hj _ ⟨index, bad, result, rfl⟩
    have hid := hids j hj
    have hIdRead := hreadIds j hj
    have hValueRead := hreadValues _ hid
    have hValueBounds := abs_le.mp (hvalues _ hid)
    have hf := flag_le_one ids values scan target targetN scanN j sign
    have hc :=
      LightColoredTwoSum.meets (d := d + 1) (values (ids j)) sign htwo hlookup hsearch μ scan target hw hscanSpace
        htargetSpace hspace hword hscan (hvalues _ hid) hsign hvalueWord hreadScan hreadTarget hpowers hsorted hL
        htargetN (by omega)
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
      refine _root_.Light.Ends.setToThen (ids j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hIdRead,
              LightColoredTwoSum.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hIdRead, LightColoredTwoSum.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hIdRead, LightColoredTwoSum.time] <;> omega)
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
      refine _root_.Light.Ends.setToThen (values (ids j)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hValueRead,
              LightColoredTwoSum.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hValueRead, LightColoredTwoSum.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hValueRead, LightColoredTwoSum.time] <;>
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
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightColoredTwoSum.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightColoredTwoSum.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColoredTwoSum.time] <;> omega)
      on_goal -1 => (rintro out ν ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν
    have hfound := LightColoredTwoSum.flag_le_one scan target targetN scanN (values (ids j)) sign
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
        _root_.Light.Ends.iteIffThen
          ((0 : ℤ) < (LightColoredTwoSum.flag scan target targetN scanN (values (ids j)) sign : ℤ)) (fun hp => ?_)
          (fun hn => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout,
              LightColoredTwoSum.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, LightColoredTwoSum.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, LightColoredTwoSum.time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hcurrent : LightColoredTwoSum.Hit scan target targetN scanN (values (ids j)) sign :=
        by
        by_contra hh
        simp [LightColoredTwoSum.flag, hh] at hp
      have hnext : flag ids values scan target targetN scanN (j + 1) sign = 1 :=
        by
        unfold flag
        rw [if_pos ((hit_succ ids values scan target targetN scanN j sign).mpr (Or.inr hcurrent))]
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightColoredTwoSum.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightColoredTwoSum.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColoredTwoSum.time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, (ids j : ℤ), values (ids j), out, ?_⟩
      simp [update_frame_setLocal, hnext]
    · have hcurrent : ¬LightColoredTwoSum.Hit scan target targetN scanN (values (ids j)) sign :=
        by
        intro hh
        simp [LightColoredTwoSum.flag, hh] at hn
      have hnext :
        flag ids values scan target targetN scanN (j + 1) sign = flag ids values scan target targetN scanN j sign := by
        simp only [flag, hit_succ, or_false, hcurrent]
      refine Ends.skip ⟨by simp, (ids j : ℤ), values (ids j), out, ?_⟩
      simp [update_frame_setLocal, hnext]
  case done => intro σ _ hshape; exact hshape
  case bound =>
    rintro j _ hj _ ⟨index, bad, result, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨index, bad, result, rfl⟩
    have hf := flag_le_one ids values scan target targetN scanN badN sign
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (flag ids values scan target targetN scanN badN sign : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, rfl⟩
end ThreeSum.LightDeletedTwoSum

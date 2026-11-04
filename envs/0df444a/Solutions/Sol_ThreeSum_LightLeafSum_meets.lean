-- Prove2me | solution 1 for ThreeSum.LightLeafSum.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:00:38.144209+00:00
-- url     : https://prove2.me/submissions/d776d161-2427-415c-9a40-cae0a2121dcb

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_succ
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_getElem
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_take_map_le
import Theorems.Thm_ThreeSumApsp_AbsLe_getElem
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sdiff_int
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
import Theorems.Thm_ThreeSum_SignedLeaf_abs_value_le
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_length
attribute [local simp] ThreeSum.LightWeightedEnumeration.output_zero
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_succ
attribute [local simp] ThreeSum.LightWeightedEnumeration.total_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.QueryCoordinates.mem_positions
attribute [local simp] ThreeSum.QueryCoordinates.missingSets_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_length
attribute [local simp] ThreeSum.QueryCoordinates.positions_toFinset
attribute [local simp] ThreeSum.QueryCoordinates.positions_zero
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_length
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_sum
attribute [local simp] ThreeSum.QueryCoordinates.selectedPowers_zero
attribute [local simp] ThreeSum.QueryCoordinates.setLayer_length
attribute [local simp] ThreeSum.QueryCoordinates.total_weights
attribute [local simp] ThreeSum.SignedLeaf.mem_explicitMissing
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
set_option autoImplicit false
open ThreeSum ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightLeafSum
theorem _root_.solution
    {pMain pLeaf pLookup pSign pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pLeaf)) (hLeaf : P[pLeaf]? = some (LightSignedLeaf.body pLookup pSign))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)) (hSign : P[pSign]? = some LightSign.body)
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) {μ : ℕ → ℤ}
    {W cut stage t maskBase baseL baseR work B D d : ℕ} (Q preL preR : Finset (Fin W)) (missing : List (Finset (Fin W)))
    (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL + (W + 1) * downsetCap W cut ≤ work) (hdataR : baseR + (W + 1) * downsetCap W cut ≤ work)
    (hmasks : maskBase + missing.length ≤ work) (hspace : work + tableSize W + (W + 1) ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word) (hdisjL : Disjoint preL Q)
    (hdisjR : Disjoint preR Q) (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B) (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t) (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W) (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d + W + 7 ≤ lim.depth) :
    Meets lim P pMain d
      [W, cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, Q.card, subsetMask Q, t, missing.length,
        maskBase, baseL, baseR, work]
      μ (time W missing.length) (fun r μ' => r = (missing.map (term Q preL preR f g stage)).sum ∧ Kept μ μ' work) :=
  by
  have hQcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hQmask : (subsetMask Q : ℤ) ≤ lim.word :=
    by
    have hp : subsetMask Q ≤ (W + 1) * 2 ^ (W + 1) :=
      (Nat.le_of_lt (subsetMask_isMask Q).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask Q : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hflagsL (U : Finset (Fin W)) : (preL ∪ (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL) Finset.sdiff_subset)).trans hcardL
  have hflagsR (U : Finset (Fin W)) : (preR ∪ (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR) Finset.sdiff_subset)).trans hcardR
  have htermBound : ∀ U ∈ missing, |term Q preL preR f g stage U| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    by
    intro U _
    exact SignedLeaf.abs_value_le f g stage preL preR (Q \ U) hstage (hflagsL U) (hflagsR U) hf hg
  have hacc (j : ℕ) : |partialSum Q preL preR f g stage missing j| ≤ lim.word :=
    by
    have hh := List.abs_sum_take_map_le missing (term Q preL preR f g stage) htermBound j
    exact hh.trans (by simpa only [Nat.cast_mul] using haccWord)
  have haddr {base : ℕ} (hdata : base + (W + 1) * downsetCap W cut ≤ work) (j : ℕ) (hj : j ≤ W) (S : Finset (Fin W))
    (hS : S.card ≤ cut) : LightZetaStages.stageBase base (downsetCap W cut) j + subsetRank S < work :=
    by
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
    unfold LightZetaStages.stageBase
    simp only [Nat.succ_mul] at hm hdata
    omega
  apply Meets.of_body hmain
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := missing.length * (LightSignedLeaf.time W + 50) + 20) (Q :=
        Inv μ Q preL preR f g stage missing cut t maskBase baseL baseR work missing.length)
        (Inv μ Q preL preR f g stage missing cut t maskBase baseL baseR work) missing.length
        (LightSignedLeaf.time W + 40) ?start ?round ?done ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega))))
      ?after
  case start =>
    refine ⟨0, μ, ?_, SameOn.refl⟩
    simp [update_frame_setLocal, partialSum]
    change
      frame
          [(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, Q.card, subsetMask Q, t,
            missing.length, maskBase, baseL, baseR, work, 0, 0] =
        frame
          ([(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, Q.card, subsetMask Q, t,
              missing.length, maskBase, baseL, baseR, work, 0, 0] ++
            [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hkeep⟩
    let U := missing[j]
    have hu := hvalid U (List.getElem_mem hj)
    have hstoredL' : LightZetaStages.StoredThrough μ' baseL cut f W :=
      by
      intro i hi S hS
      exact (hkeep _ (haddr hdataL i hi S hS)).trans (hstoredL i hi S hS)
    have hstoredR' : LightZetaStages.StoredThrough μ' baseR cut g W :=
      by
      intro i hi S hS
      exact (hkeep _ (haddr hdataR i hi S hS)).trans (hstoredR i hi S hS)
    have hmask : μ' (maskBase + j) = (subsetMask U : ℤ) :=
      by
      have hr := hseg.getElem (by simpa using hj)
      simp only [List.getElem_map] at hr
      exact (hkeep _ (by omega)).trans hr
    have hcard : (Q \ U).card = Q.card - t := by rw [Finset.card_sdiff_of_subset hu.1, hu.2]
    have hmaskSub := MaskDifference.subsetMask_sdiff_int Q U hu.1
    have hcardInt : (Q.card : ℤ) - (t : ℤ) = ((Q \ U).card : ℤ) := by
      rw [hcard, Int.ofNat_sub (by rw [← hu.2]; exact Finset.card_le_card hu.1)]
    have hc :=
      LightSignedLeaf.meets (d := d + 1) hLeaf hLookup hSign hSize hAddress C hOffset preL preR (Q \ U) f g hw hcut
        hstage hdataL hdataR hspace hword hproductWord (hdisjL.mono_right Finset.sdiff_subset)
        (hdisjR.mono_right Finset.sdiff_subset) (hflagsL U) (hflagsR U) hf hg hstoredL' hstoredR' (by omega)
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask, hmaskSub,
              hcardInt, LightSignedLeaf.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmask, hmaskSub, hcardInt, LightSignedLeaf.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, hmaskSub, hcardInt,
              LightSignedLeaf.time] <;> omega)
      on_goal -1 => (rintro res μ₁ ⟨hres, hnewKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hnext := abs_le.mp (hacc (j + 1))
    have hsum :
      partialSum Q preL preR f g stage missing j + term Q preL preR f g stage U =
        partialSum Q preL preR f g stage missing (j + 1) :=
      (partialSum_succ Q preL preR f g stage missing hj).symm
    have hres' : res = term Q preL preR f g stage U := hres
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (partialSum Q preL preR f g stage missing (j + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres', hsum,
              LightSignedLeaf.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hres', hsum, LightSignedLeaf.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres', hsum, LightSignedLeaf.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, res, μ₁, ?_, hkeep.trans hnewKeep⟩
    simp [update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨r, μ', rfl, hkeep⟩
    have ha := abs_le.mp (hacc missing.length)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen ((missing.map (term Q preL preR f g stage)).sum) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, partialSum_length]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [partialSum_length] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, partialSum_length] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, hkeep⟩
end ThreeSum.LightLeafSum

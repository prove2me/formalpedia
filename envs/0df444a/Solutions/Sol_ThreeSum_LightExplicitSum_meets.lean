-- Prove2me | solution 1 for ThreeSum.LightExplicitSum.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:08:03.794471+00:00
-- url     : https://prove2.me/submissions/71700af7-2c09-44af-968c-b34cf5703ac2

import Definitions.Def_Submission_ThreeSum_ExplicitLayers
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_ExplicitLayers_choose_le_offset
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_abs_le
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_succ
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeaf_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_mem
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
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_mono
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
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
attribute [local simp] ThreeSum.ExplicitLayers.leaves_length
attribute [local simp] ThreeSum.ExplicitLayers.missing_length
attribute [local simp] ThreeSum.ExplicitLayers.valueSum_zero
attribute [local simp] ThreeSum.LightLeafSum.partialSum_length
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightExplicitSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightExplicitSum
theorem _root_.solution {pMain pEnum pSum : ℕ} (hmain : P[pMain]? = some (body pEnum pSum)) (C : Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ} (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL + (W + 1) * downsetCap W cut ≤ maskBase) (hdataR : baseR + (W + 1) * downsetCap W cut ≤ maskBase)
    (hmasks : maskBase + layerOffset Q.card t ≤ work) (hspace : work + tableSize W + (W + 1) ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card + 1) (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q) (hcardL : (preL ∪ Q).card ≤ cut)
    (hcardR : (preR ∪ Q).card ≤ cut) (hf : ∀ T, T.card ≤ cut → |f T| ≤ B) (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W) (hd : d + W + 8 ≤ lim.depth) :
    Meets lim P pMain d
      [W, cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, Q.card, subsetMask Q, t, baseL, baseR,
        maskBase, work]
      μ (time W Q.card t)
      (fun r μ' =>
        r = ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) t ∧
          KeptBut μ μ' work maskBase (layerOffset Q.card t)) :=
  by
  have hQcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have henumSpace : work + (2 * W + 2) ≤ lim.space := by unfold tableSize at hspace; nlinarith
  have henumWord : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ (W + 1) : ℕ) ≤ (W + 1) * 2 ^ (W + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh := Nat.le_mul_of_pos_left ((2 ^ stage * B) * (2 ^ stage * D)) (by omega : 0 < layerOffset Q.card t + 1)
    exact
      (by exact_mod_cast hh :
            (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤
              (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ)).trans
        haccWord
  have hweight (S : Finset (Fin W)) (hS : S ⊆ Q) :
    |SignedLeaf.value f g stage preL preR S| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    SignedLeaf.abs_value_le f g stage preL preR S hstage
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL) hS)).trans hcardL)
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR) hS)).trans hcardR) hf hg
  have hacc (j : ℕ) (hj : j ≤ t) : |ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) j| ≤ lim.word :=
    by
    have hh := ExplicitLayers.valueSum_abs_le Q (SignedLeaf.value f g stage preL preR) j hweight
    have hn :
      layerOffset Q.card j * ((2 ^ stage * B) * (2 ^ stage * D)) ≤
        (layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) :=
      Nat.mul_le_mul_right _ ((layerOffset_mono Q.card hj).trans (Nat.le_succ _))
    have hz :
      ((layerOffset Q.card j * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤
        (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) :=
      by exact_mod_cast hn
    exact hh.trans (hz.trans haccWord)
  have haddr {base : ℕ} (hdata : base + (W + 1) * downsetCap W cut ≤ maskBase) (j : ℕ) (hj : j ≤ W) (S : Finset (Fin W))
    (hS : S.card ≤ cut) : LightZetaStages.stageBase base (downsetCap W cut) j + subsetRank S < maskBase :=
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
      (Ends.for (T := t * (roundTime W Q.card t + 20) + 20) (Q :=
        Inv μ Q preL preR f g stage cut t baseL baseR maskBase work t)
        (Inv μ Q preL preR f g stage cut t baseL baseR maskBase work) t (roundTime W Q.card t) ?start ?round ?done
        ?bound (hT := by
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
    refine ⟨0, 0, μ, ?_, SameOn.refl⟩
    simp [update_frame_setLocal]
    change
      frame
          [(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, Q.card, subsetMask Q, t, baseL,
            baseR, maskBase, work, 0, 0] =
        frame
          ([(W : ℤ), cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, Q.card, subsetMask Q, t, baseL,
              baseR, maskBase, work, 0, 0] ++
            [0, 0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨count, r, μ', rfl, hkeep⟩
    have hcap := ExplicitLayers.choose_le_offset (c := Q.card) hj
    have hEnumTime : LightQueryEnumeration.time W Q.card j ≤ 1400 * (W + 1) ^ 2 * (layerOffset Q.card t + 1) :=
      (LightQueryEnumeration.time_bound hQcard).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hcap))
    have hSumTime : LightLeafSum.time W (Q.card.choose j) ≤ 5900 * (W + 1) ^ 2 * (layerOffset Q.card t + 1) :=
      (LightLeafSum.time_bound W _).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hcap))
    have hp : 1 ≤ (W + 1) ^ 2 * (layerOffset Q.card t + 1) := Nat.mul_pos (by positivity) (by omega)
    have hround :
      LightQueryEnumeration.time W Q.card j + LightLeafSum.time W (Q.card.choose j) + 100 ≤ roundTime W Q.card t :=
      by
      unfold roundTime
      nlinarith
    have he :=
      LightQueryEnumeration.meets (d := d + 1) (μ := μ') (t := j) (dst := maskBase) (work := work) C.enumerate C.weights
        C.table.powers C.erase C.core Q hw henumSpace henumWord (by omega) (by omega) (by omega)
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
      | refine _root_.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen he ?_ ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      on_goal -1 =>
        (rintro newCount μ₁ ⟨hcount, hmaskSeg, _, hkeepEnum⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hkeep₁ : KeptBut μ μ₁ work maskBase (layerOffset Q.card t) :=
      by
      intro i hi
      exact (hkeepEnum i ⟨hi.1, by rcases hi.2 with h | h <;> omega⟩).trans (hkeep i hi)
    have hstoredL₁ : LightZetaStages.StoredThrough μ₁ baseL cut f W :=
      by
      intro i hi S hS
      have ha := haddr hdataL i hi S hS
      exact (hkeep₁ _ ⟨by omega, Or.inl ha⟩).trans (hstoredL i hi S hS)
    have hstoredR₁ : LightZetaStages.StoredThrough μ₁ baseR cut g W :=
      by
      intro i hi S hS
      have ha := haddr hdataR i hi S hS
      exact (hkeep₁ _ ⟨by omega, Or.inl ha⟩).trans (hstoredR i hi S hS)
    have hsumWord : (((missingSets Q j).length * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word :=
      by
      have hn := Nat.mul_le_mul_right ((2 ^ stage * B) * (2 ^ stage * D)) (hcap.trans (Nat.le_succ _))
      have hz :
        ((Q.card.choose j * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤
          (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) :=
        by exact_mod_cast hn
      simpa only [missingSets_length] using hz.trans haccWord
    have hs :=
      LightLeafSum.meets (d := d + 1) (μ := μ₁) C.sum C.leaf C.lookup C.sign C.size C.address C.table C.offset Q preL
        preR (missingSets Q j) f g hw hcut hstage (by omega) (by omega)
        (by simpa using (show maskBase + Q.card.choose j ≤ work by omega)) hspace hword hproductWord hsumWord hdisjL
        hdisjR hcardL hcardR hf hg (fun U hU => (missingSets_mem Q U j).mp hU) hstoredL₁ hstoredR₁ hmaskSeg (by omega)
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
      | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount,
              missingSets_length]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcount, missingSets_length] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, missingSets_length] <;> omega)
      on_goal -1 => (rintro res μ₂ ⟨hres, hkeepSum⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hnext := abs_le.mp (hacc (j + 1) (by omega))
    have hres' : res = ((missingSets Q j).map fun U => SignedLeaf.value f g stage preL preR (Q \ U)).sum := hres
    have hsucc := ExplicitLayers.valueSum_succ Q (SignedLeaf.value f g stage preL preR) j
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine
        _root_.Light.Ends.setToThen (ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) (j + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres', hsucc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hres', hsucc] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres', hsucc] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, newCount, res, μ₂, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hkeepSum i hi.1).trans (hkeep₁ i hi)
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨count, r, μ', rfl, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨count, r, μ', rfl, hkeep⟩
    have ha := abs_le.mp (hacc t le_rfl)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) t) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, hkeep⟩
end ThreeSum.LightExplicitSum

-- Prove2me | solution 1 for ThreeSum.LightSignedLeafBatch.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:21:25.532843+00:00
-- url     : https://prove2.me/submissions/bb6ee676-ea96-4ec8-bc8a-c2583a95add0

import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightSignedLeafBatch
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_storedThrough_of_on
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
import Definitions.Def_WeightedCache3SUM_Alias_c287aeb916bf4368
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
import Theorems.Thm_ThreeSum_LightSignedLeafCell_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9b8d9638683d951
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
import Theorems.Thm_ThreeSum_MaskDecode_decode_card
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_all
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_zero
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
import Theorems.Thm_ThreeSum_SignedLeaf_mem_explicitMissing
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_injective
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_injective
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
attribute [local simp] ThreeSum.MaskUnion.scanSet_all
attribute [local simp] ThreeSum.MaskUnion.scanSet_zero
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
open ThreeSum ThreeSum.LightSignedLeafBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeafBatch
theorem _root_.solution {pMain pCell pLeaf pAddress : ℕ} (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightSignedLeafCell.body pLeaf pAddress))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress) {μ : ℕ → ℤ}
    {W sourceCut boxCut stage cardinal maskBase baseL baseR dst work B D d : ℕ} (masks : List ℕ)
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W)
    (hstage : stage ≤ W) (hdataL : baseL + (W + 1) * downsetCap W sourceCut ≤ work)
    (hdataR : baseR + (W + 1) * downsetCap W sourceCut ≤ work) (hdst : dst + downsetCap W boxCut ≤ work)
    (hmasks : maskBase + masks.length ≤ work)
    (hsepL : Apart baseL ((W + 1) * downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hsepR : Apart baseR ((W + 1) * downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hsepMasks : Apart maskBase masks.length dst (downsetCap W boxCut))
    (hspace : work + 1 + LightPascal.tableSize W + (W + 1) ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word) (hpreL : preL.card + boxCut ≤ sourceCut)
    (hpreR : preR.card + boxCut ≤ sourceCut) (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D) (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W) (hseg : SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, IsMask W cardinal m) (hcardinal : cardinal ≤ boxCut) (hd : d + W + 8 ≤ lim.depth) :
    Meets lim P pMain d
      [W, sourceCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, cardinal, masks.length, maskBase,
        baseL, baseR, dst, work]
      μ (time W masks.length)
      (fun _ μ' =>
        TableAt μ' dst boxCut (values μ dst masks (SignedLeaf.value f g stage preL preR)) ∧
          KeptBut μ μ' work dst (downsetCap W boxCut)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ sourceCut boxCut stage cardinal maskBase baseL baseR dst work masks preL preR f g) masks.length
      (LightSignedLeafCell.time W + 40) ?start ?round ?done ?bound (hT := by
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
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, SameOn.refl, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame
            [(W : ℤ), sourceCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, cardinal, masks.length,
              maskBase, baseL, baseR, dst, work, 0] =
          frame
            ([(W : ℤ), sourceCut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, cardinal, masks.length,
                maskBase, baseL, baseR, dst, work, 0] ++
              [0])
      exact (frame_append_zeros _ 1).symm
    · intro S hS
      simp [values]
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hkept, hout⟩
    let m := masks[j]
    have hm : IsMask W cardinal m := hvalid m (List.getElem_mem hj)
    let S := decode W m
    have hScard : S.card = cardinal := by
      dsimp only [S]
      rw [decode_card hm.1, hm.2]
    have hSmask : subsetMask S = m := subsetMask_decode hm.1
    have hS : S.card ≤ boxCut := hScard.trans_le hcardinal
    have hrS := subsetRank_lt hS
    have hL : (preL ∪ S).card ≤ sourceCut := (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hS _).trans hpreL)
    have hR : (preR ∪ S).card ≤ sourceCut := (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hS _).trans hpreR)
    have hsourceL : LightZetaStages.StoredThrough μ' baseL sourceCut f W :=
      storedThrough_of_on hstoredL
        (by
          intro i hi₀ hi₁
          exact hkept i ⟨by omega, by omega⟩)
    have hsourceR : LightZetaStages.StoredThrough μ' baseR sourceCut g W :=
      storedThrough_of_on hstoredR
        (by
          intro i hi₀ hi₁
          exact hkept i ⟨by omega, by omega⟩)
    have hmaskread : μ' (maskBase + j) = (m : ℤ) := (hkept _ ⟨by omega, by omega⟩).trans (hseg.getElem hj)
    have hc :=
      LightSignedLeafCell.meets (d := d + 1) hcell C preL preR S f g hw hcut hstage hdataL hdataR hdst hspace hword
        hproductWord hS hL hR hf hg hsourceL hsourceR (by omega)
    rw [hScard, hSmask] at hc
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmaskread,
              LightSignedLeafCell.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmaskread, LightSignedLeafCell.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmaskread, LightSignedLeafCell.time] <;> omega)
      on_goal -1 => (rintro res μ'' ⟨hnew, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, res, μ'', ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hkeep i hi.1 (by omega)).trans (hkept i hi)
    · intro T hT
      have hrT := subsetRank_lt hT
      have htake : masks.take (j + 1) = masks.take j ++ [m] := by
        simpa only [m] using List.take_succ_eq_append_getElem (l := masks) hj
      by_cases heq : T = S
      · subst T
        rw [hnew]
        simp [values, htake, hSmask]
      · have hrne : dst + subsetRank T ≠ dst + subsetRank S :=
          by
          intro hh
          exact heq (subsetRank_injective W (Nat.add_left_cancel hh))
        have hmne : subsetMask T ≠ m := by
          intro hh
          exact heq (subsetMask_injective W (hh.trans hSmask.symm))
        rw [hkeep _ (by omega) hrne, hout T hT]
        simp only [values, htake, List.mem_append, List.mem_singleton, hmne, or_false]
  case done =>
    rintro _ _ ⟨r, μ', rfl, hkept, hout⟩
    exact ⟨by simpa only [List.take_length] using hout, hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightSignedLeafBatch

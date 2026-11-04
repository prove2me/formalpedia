-- Prove2me | solution 1 for ThreeSum.LightSignedLeaf.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:13.786285+00:00
-- url     : https://prove2.me/submissions/c8223403-bd79-48b2-bc79-2aceeae5f31c

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightSign
import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
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
import Definitions.Def_WeightedCache3SUM_Alias_ed0b475cc4fc86b4
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_3cbba57b9f47c556
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
import Theorems.Thm_ThreeSum_SignedLeaf_subsetMask_disjoint_union
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Definitions.Def_WeightedCache3SUM_Alias_8b6c5b6059fc82de
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeaf
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeaf
theorem _root_.solution {pMain pLookup pSign pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pLookup pSign))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)) (hSign : P[pSign]? = some LightSign.body)
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) {μ : ℕ → ℤ} {W cut stage baseL baseR work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W)
    (hstage : stage ≤ W) (hdataL : baseL + (W + 1) * downsetCap W cut ≤ work)
    (hdataR : baseR + (W + 1) * downsetCap W cut ≤ work) (hspace : work + tableSize W + (W + 1) ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) ≤ lim.word) (hdisjL : Disjoint preL S)
    (hdisjR : Disjoint preR S) (hcardL : (preL ∪ S).card ≤ cut) (hcardR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B) (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W) (hd : d + W + 6 ≤ lim.depth) :
    Meets lim P pMain d
      [W, cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, S.card, subsetMask S, baseL, baseR, work]
      μ (time W) (fun r μ' => r = SignedLeaf.value f g stage preL preR S ∧ Kept μ μ' work) :=
  by
  have hScard : S.card ≤ W := by simpa using Finset.card_le_univ S
  have hCL : preL.card + S.card = (preL ∪ S).card := (Finset.card_union_of_disjoint hdisjL).symm
  have hCR : preR.card + S.card = (preR ∪ S).card := (Finset.card_union_of_disjoint hdisjR).symm
  have hML : subsetMask preL + subsetMask S = subsetMask (preL ∪ S) :=
    (SignedLeaf.subsetMask_disjoint_union preL S hdisjL).symm
  have hMR : subsetMask preR + subsetMask S = subsetMask (preR ∪ S) :=
    (SignedLeaf.subsetMask_disjoint_union preR S hdisjR).symm
  have hmaskWord (T : Finset (Fin W)) : (subsetMask T : ℤ) ≤ lim.word :=
    by
    have hp : subsetMask T ≤ (W + 1) * 2 ^ (W + 1) :=
      (Nat.le_of_lt (subsetMask_isMask T).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask T : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  have haddrR : LightStageLookup.readAddr cut baseR stage (preR ∪ S) < work :=
    by
    have hr := subsetRank_lt hcardR
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hstage)
    unfold LightStageLookup.readAddr
    simp only [Nat.succ_mul] at hm hdataR
    omega
  have hreadL : μ (LightStageLookup.readAddr cut baseL stage (preL ∪ S)) = SubsetStages.stageValue f stage (preL ∪ S) :=
    by simpa only [LightStageLookup.readAddr, LightZetaStages.stageBase] using hstoredL stage hstage _ hcardL
  have hreadR : μ (LightStageLookup.readAddr cut baseR stage (preR ∪ S)) = SubsetStages.stageValue g stage (preR ∪ S) :=
    by simpa only [LightStageLookup.readAddr, LightZetaStages.stageBase] using hstoredR stage hstage _ hcardR
  have hproduct :
    |SubsetStages.stageValue f stage (preL ∪ S) * SubsetStages.stageValue g stage (preR ∪ S)| ≤ lim.word :=
    by
    rw [abs_mul]
    have h₁ := SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hcardL
    have h₂ := SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hcardR
    have hh := mul_le_mul h₁ h₂ (abs_nonneg _) (Int.natCast_nonneg _)
    exact hh.trans (by simpa only [Nat.cast_mul] using hproductWord)
  have hmaskLWord := hmaskWord (preL ∪ S)
  have hmaskRWord := hmaskWord (preR ∪ S)
  apply Meets.of_body hmain
  unfold body time
  have hcL :=
    LightStageLookup.meets (d := d + 1) (μ := μ) hLookup hSize hAddress C hOffset (preL ∪ S) _ hw hcut hdataL hspace
      hword hcardL hstage hreadL (by omega)
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
    | refine _root_.Light.Ends.callToThen (hcL _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcL ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hCL, hML, LightStageLookup.time,
            LightSign.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hCL, hML, LightStageLookup.time, LightSign.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hCL, hML, LightStageLookup.time,
            LightSign.time] <;> omega)
    on_goal -1 => (rintro left μ₁ ⟨hleft, hkeepL⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hreadR₁ :
    μ₁ (LightStageLookup.readAddr cut baseR stage (preR ∪ S)) = SubsetStages.stageValue g stage (preR ∪ S) :=
    (hkeepL _ haddrR).trans hreadR
  have hcR :=
    LightStageLookup.meets (d := d + 1) (μ := μ₁) hLookup hSize hAddress C hOffset (preR ∪ S) _ hw hcut hdataR hspace
      hword hcardR hstage hreadR₁ (by omega)
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
    | refine _root_.Light.Ends.callToThen (hcR _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcR ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hCR, hMR, LightStageLookup.time,
            LightSign.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hCR, hMR, LightStageLookup.time, LightSign.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hCR, hMR, LightStageLookup.time,
            LightSign.time] <;> omega)
    on_goal -1 => (rintro right μ₂ ⟨hright, hkeepR⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpBound := abs_le.mp hproduct
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
      _root_.Light.Ends.setToThen
        (SubsetStages.stageValue f stage (preL ∪ S) * SubsetStages.stageValue g stage (preR ∪ S)) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hleft, hright, LightStageLookup.time,
            LightSign.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hleft, hright, LightStageLookup.time, LightSign.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hleft, hright, LightStageLookup.time,
            LightSign.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hsign := LightSign.meets (d := d + 1) (μ := μ₂) (e := S.card) hSign hw (by omega) hproduct
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
    | refine _root_.Light.Ends.callToThen (hsign _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsign ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightStageLookup.time, LightSign.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightStageLookup.time, LightSign.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightStageLookup.time, LightSign.time] <;> omega)
    on_goal -1 => (rintro res μ₃ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₃
  exact ⟨hres, hkeepL.trans hkeepR⟩
end ThreeSum.LightSignedLeaf

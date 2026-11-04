-- Prove2me | solution 1 for ThreeSum.LightSparseQuery.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:27:10.156208+00:00
-- url     : https://prove2.me/submissions/8b908db1-6f2d-4ea0-8786-68a68cbb6a5f

import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Definitions.Def_Submission_ThreeSum_LightSparseQuery
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_le_sum_abs
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_ExplicitLayers_leaves_length
import Theorems.Thm_ThreeSum_ExplicitLayers_missing_length
import Theorems.Thm_ThreeSum_ExplicitLayers_sparse_identity
import Theorems.Thm_ThreeSum_ExplicitLayers_valueSum_zero
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_84a6d1c69132a490
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Theorems.Thm_ThreeSum_LightExplicitSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_meets
import Theorems.Thm_ThreeSum_LightLeafSum_partialSum_length
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
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
import Theorems.Thm_ThreeSum_SignedLeaf_mobius_eq_signed_sum
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
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
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
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
open ThreeSum ThreeSum.LightSparseQuery
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open scoped BigOperators
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSparseQuery
theorem _root_.solution {pMain pExplicit pBoxes pSign pEnum pLeafSum pBoxSum : ℕ}
    (hmain : P[pMain]? = some (body pExplicit pBoxes pSign))
    (hExplicit : P[pExplicit]? = some (LightExplicitSum.body pEnum pLeafSum))
    (hBoxes : P[pBoxes]? = some (LightCanonicalBoxSum.body pEnum pBoxSum)) (hSign : P[pSign]? = some LightSign.body)
    (CE : LightExplicitSum.Procs P pEnum pLeafSum) (CB : LightCanonicalBoxSum.Procs P pEnum pBoxSum) {μ : ℕ → ℤ}
    {W cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ} (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL + (W + 1) * downsetCap W cut ≤ maskBase) (hdataR : baseR + (W + 1) * downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase + (W + 1) * downsetCap W boxCut ≤ maskBase) (hmasks : maskBase + queryItems Q.card t ≤ work)
    (hspace : work + tableSize W + (W + 1) ≤ lim.space) (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (magnitudeBound W stage Q.card t B D : ℤ) ≤ lim.word) (ht : t ≤ Q.card + 1)
    (hboxCut : boxCut ≤ Q.card) (hflags : Q.card - t ≤ boxCut) (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut) (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D) (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut (SignedLeaf.value f g stage preL preR) W)
    (hd : d + W + 9 ≤ lim.depth) :
    Meets lim P pMain d
      [W, cut, stage, preL.card, subsetMask preL, preR.card, subsetMask preR, Q.card, subsetMask Q, t, baseL, baseR,
        boxCut, boxBase, maskBase, work]
      μ (time W Q.card t)
      (fun r μ' =>
        r =
            Subset.mobius
              (fun S => SubsetStages.stageValue f stage (preL ∪ S) * SubsetStages.stageValue g stage (preR ∪ S)) Q ∧
          KeptBut μ μ' work maskBase (queryItems Q.card t)) :=
  by
  have hQcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hboxW : boxCut ≤ W := hboxCut.trans hQcard
  have hoff : layerOffset Q.card t ≤ queryItems Q.card t := by unfold queryItems; omega
  have hchoose : Q.card.choose t ≤ queryItems Q.card t := by unfold queryItems; omega
  have hpow : 1 ≤ (2 ^ W : ℕ) := Nat.one_le_pow' W 1
  have hproduct : (2 ^ stage * B) * (2 ^ stage * D) ≤ 2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D)) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)
  have hfullBound : 2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D)) ≤ magnitudeBound W stage Q.card t B D :=
    Nat.le_mul_of_pos_left _ (by unfold queryItems; omega)
  have heBound :
    (layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) ≤ magnitudeBound W stage Q.card t B D :=
    Nat.mul_le_mul (Nat.succ_le_succ hoff) hproduct
  have hbBound :
    Q.card.choose t * (2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D))) ≤ magnitudeBound W stage Q.card t B D :=
    Nat.mul_le_mul_right _ (hchoose.trans (Nat.le_succ _))
  have hExplicitWord : (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast heBound :
          (((layerOffset Q.card t + 1) * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤
            (magnitudeBound W stage Q.card t B D : ℤ)).trans
      hvalueWord
  have hBoxWord : ((Q.card.choose t * (2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D))) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbBound :
          ((Q.card.choose t * (2 ^ W * ((2 ^ stage * B) * (2 ^ stage * D))) : ℕ) : ℤ) ≤
            (magnitudeBound W stage Q.card t B D : ℤ)).trans
      hvalueWord
  have hCL : preL.card + Q.card ≤ cut := by rwa [Finset.card_union_of_disjoint hdisjL] at hcardL
  have hCR : preR.card + Q.card ≤ cut := by rwa [Finset.card_union_of_disjoint hdisjR] at hcardR
  have hweight (S : Finset (Fin W)) (hS : S.card ≤ Q.card) :
    |SignedLeaf.value f g stage preL preR S| ≤ (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
    by
    apply SignedLeaf.abs_value_le (cut := cut) f g stage preL preR S hstage
    · exact (Finset.card_union_le preL S).trans (by omega)
    · exact (Finset.card_union_le preR S).trans (by omega)
    · exact hf
    · exact hg
  have htotal : |∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S| ≤ lim.word :=
    by
    have hs :
      |∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S| ≤
        ((2 ^ Q.card * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) :=
      by
      calc
        _ ≤ ∑ S ∈ Q.powerset, |SignedLeaf.value f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _S ∈ Q.powerset, (((2 ^ stage * B) * (2 ^ stage * D) : ℕ) : ℤ) :=
          (Finset.sum_le_sum fun S hS => hweight S (Finset.card_le_card (Finset.mem_powerset.mp hS)))
        _ = _ := by simp [Nat.cast_mul]
    have hn : 2 ^ Q.card * ((2 ^ stage * B) * (2 ^ stage * D)) ≤ magnitudeBound W stage Q.card t B D :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hQcard)).trans hfullBound
    have hz :
      ((2 ^ Q.card * ((2 ^ stage * B) * (2 ^ stage * D)) : ℕ) : ℤ) ≤ (magnitudeBound W stage Q.card t B D : ℤ) := by
      exact_mod_cast hn
    exact hs.trans (hz.trans hvalueWord)
  apply Meets.of_body hmain
  unfold body time
  have he :=
    LightExplicitSum.meets (d := d + 1) (μ := μ) (t := t) (baseL := baseL) (baseR := baseR) (maskBase := maskBase)
      (work := work) hExplicit CE Q preL preR f g hw hcut hstage hdataL hdataR (by omega) hspace hword hExplicitWord ht
      hdisjL hdisjR hcardL hcardR hf hg hstoredL hstoredR (by omega)
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro explicit μ₁ ⟨heValue, hkeepE⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hstoredBox₁ : LightBoxStages.StoredThrough μ₁ boxBase boxCut (SignedLeaf.value f g stage preL preR) W :=
    by
    intro j hj S hS
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap W boxCut) (Nat.succ_le_succ hj)
    have ha : LightBoxStages.stageBase boxBase (downsetCap W boxCut) j + subsetRank S < maskBase :=
      by
      unfold LightBoxStages.stageBase
      simp only [Nat.succ_mul] at hm hdataBox
      omega
    exact (hkeepE _ ⟨by omega, Or.inl ha⟩).trans (hstoredBox j hj S hS)
  have hb :=
    LightCanonicalBoxSum.meets (d := d + 1) (μ := μ₁) (t := t) (base := boxBase) (maskBase := maskBase) (work := work)
      hBoxes CB Q (SignedLeaf.value f g stage preL preR) hw hboxW hdataBox (by omega) hspace hword hBoxWord ht hflags
      (fun S hS => hweight S (hS.trans hboxCut)) hstoredBox₁ (by omega)
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
    | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro boxes μ₂ ⟨hbValue, hkeepB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hsum : explicit + boxes = ∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S :=
    by
    rw [heValue, hbValue]
    exact (ExplicitLayers.sparse_identity Q (SignedLeaf.value f g stage preL preR) t).symm
  have htotalSides := abs_le.mp htotal
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsum]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hsum] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsum] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hs := LightSign.meets (d := d + 1) (μ := μ₂) (e := Q.card) hSign hw (by omega) htotal
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
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSign.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSign.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSign.time] <;> omega)
    on_goal -1 => (rintro res μ₃ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₃
  refine ⟨hres.trans (SignedLeaf.mobius_eq_signed_sum f g stage preL preR Q).symm, ?_⟩
  intro i hi
  exact
    (hkeepB i ⟨hi.1, by rcases hi.2 with h | h <;> omega⟩).trans (hkeepE i ⟨hi.1, by rcases hi.2 with h | h <;> omega⟩)
end ThreeSum.LightSparseQuery

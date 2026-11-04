-- Prove2me | solution 1 for ThreeSum.LightCanonicalBoxSum.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:13:12.968251+00:00
-- url     : https://prove2.me/submissions/0da77ef2-ced8-4928-9a56-503319574673

import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
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
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_443601c744eb157d
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_ThreeSum_LightBoxSum_sum_eq_canonical
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
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
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_mem
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_nodup
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_length
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_toFinset
import Theorems.Thm_ThreeSum_QueryCoordinates_positions_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_length
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_sum
import Theorems.Thm_ThreeSum_QueryCoordinates_selectedPowers_zero
import Theorems.Thm_ThreeSum_QueryCoordinates_setLayer_length
import Theorems.Thm_ThreeSum_QueryCoordinates_total_weights
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
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
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
open ThreeSum ThreeSum.LightCanonicalBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightCanonicalBoxSum
theorem _root_.solution {pMain pEnum pSum : ℕ} (hmain : P[pMain]? = some (body pEnum pSum)) (C : Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W cut t base maskBase work B d : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hdata : base + (W + 1) * downsetCap W cut ≤ maskBase)
    (hmasks : maskBase + Q.card.choose t ≤ work) (hspace : work + tableSize W + (W + 1) ≤ lim.space)
    (hword : (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((Q.card.choose t * (2 ^ W * B) : ℕ) : ℤ) ≤ lim.word) (ht : t ≤ Q.card + 1) (hflags : Q.card - t ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B) (hstored : LightBoxStages.StoredThrough μ base cut weight W)
    (hd : d + W + 8 ≤ lim.depth) :
    Meets lim P pMain d [W, cut, Q.card, subsetMask Q, t, base, maskBase, work] μ (time W Q.card t)
      (fun r μ' =>
        r = ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
          KeptBut μ μ' work maskBase (Q.card.choose t)) :=
  by
  have henumSpace : work + (2 * W + 2) ≤ lim.space :=
    by
    unfold tableSize at hspace
    nlinarith
  have henumWord : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hm : (2 ^ (W + 1) : ℕ) ≤ (W + 1) * 2 ^ (W + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hm : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ (((W + 1) * 2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have he :=
    LightQueryEnumeration.meets (d := d + 1) (μ := μ) C.enumerate C.weights C.table.powers C.erase C.core Q hw
      henumSpace henumWord ht hmasks (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryEnumeration.time,
            LightBoxSum.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryEnumeration.time, LightBoxSum.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryEnumeration.time,
            LightBoxSum.time] <;> omega)
    on_goal -1 =>
      (rintro count μ₁ ⟨hcount, hmaskSeg, _, hkeepEnum⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hstored₁ : LightBoxStages.StoredThrough μ₁ base cut weight W :=
    by
    intro j hj S hS
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
    have ha : LightBoxStages.stageBase base (downsetCap W cut) j + subsetRank S < maskBase :=
      by
      unfold LightBoxStages.stageBase
      simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul] at hm hdata
      omega
    exact (hkeepEnum _ ⟨by omega, Or.inl ha⟩).trans (hstored j hj S hS)
  have hvalid : ∀ U ∈ missingSets Q t, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut :=
    by
    intro U hU
    have hu := (missingSets_mem Q U t).mp hU
    refine ⟨hu.1, hu.2, ?_⟩
    rw [Finset.card_sdiff_of_subset hu.1, hu.2]
    exact hflags
  have hs :=
    LightBoxSum.meets (d := d + 1) (μ := μ₁) C.sum C.box C.minimum C.lookup C.size C.address C.table C.offset C.erase Q
      (missingSets Q t) weight hw hcut (by omega) (by simpa using hmasks) hspace hword (by simpa using haccWord) hvalid
      hweight hstored₁ hmaskSeg (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryEnumeration.time,
            LightBoxSum.time, hcount, missingSets_length]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryEnumeration.time, LightBoxSum.time, hcount, missingSets_length] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryEnumeration.time, LightBoxSum.time,
            hcount, missingSets_length] <;> omega)
    on_goal -1 => (rintro res μ₂ ⟨hres, hkeepSum⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_⟩
  ·
    exact
      hres.trans
        (LightBoxSum.sum_eq_canonical Q weight (missingSets Q t) (missingSets_nodup Q t)
          (fun U => by simp only [missingSets_mem, Finset.mem_powersetCard]))
  · intro i hi
    exact (hkeepSum i hi.1).trans (hkeepEnum i hi)
end ThreeSum.LightCanonicalBoxSum

-- Prove2me | solution 1 for ThreeSum.LightQueryEnumeration.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:19.535496+00:00
-- url     : https://prove2.me/submissions/7d1093fe-81cb-428e-a260-c3d633021eb6

import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightQueryWeights_weights_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_zero
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_QueryCoordinates_mem_positions
import Theorems.Thm_ThreeSum_QueryCoordinates_missingSets_length
import Definitions.Def_WeightedCache3SUM_Alias_babed7f0640a195f
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
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryEnumeration
theorem _root_.solution {pMain pWeights pPowers pErase pEnum : ℕ} (hmain : P[pMain]? = some (body pWeights pEnum))
    (hweights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)) (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum)) {μ : ℕ → ℤ} {W t dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : work + (2 * W + 2) ≤ lim.space)
    (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (ht : t ≤ Q.card + 1) (hdst : dst + Q.card.choose t ≤ work)
    (hd : d + W + 2 ≤ lim.depth) :
    Meets lim P pMain d [W, subsetMask Q, t, dst, work] μ (time W Q.card t)
      (fun r μ' =>
        r = (Q.card.choose t : ℤ) ∧
          SegN μ' dst ((missingSets Q t).map subsetMask) ∧
            LightWeightedEnumeration.Weights μ' work Q.card (weights Q) ∧ KeptBut μ μ' work dst (Q.card.choose t)) :=
  by
  have hc : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hm : (subsetMask Q : ℤ) ≤ lim.word :=
    by
    have hh : subsetMask Q ≤ 2 ^ (W + 1) :=
      (Nat.le_of_lt (subsetMask_isMask Q).1).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hh : (subsetMask Q : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
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
    refine _root_.Light.Ends.setToThen (work + W + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryWeights.time,
            LightSubsetEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryWeights.time, LightSubsetEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryWeights.time,
            LightSubsetEnumeration.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hbuild :=
    LightQueryWeights.meets (d := d + 1) (μ := μ) (dst := work) (work := work + W + 1) hweights hpowers herase Q hw
      (by omega) (by omega) hword (by omega)
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
    | refine _root_.Light.Ends.callToThen (hbuild _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hbuild ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryWeights.time,
            LightSubsetEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryWeights.time, LightSubsetEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryWeights.time,
            LightSubsetEnumeration.time] <;>
          omega)
    on_goal -1 => (rintro count μ₁ ⟨hcount, hseg, _, hkept₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hwtable := LightQueryWeights.weights_of_segment hseg
  have henumCall :=
    LightWeightedEnumeration.meets (W := Q.card) (U := subsetMask Q) henum hw (by omega) hm Q.card t 0 dst μ₁ le_rfl ht
      (by simp) hdst hwtable (d + 1) (by omega)
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
    | refine _root_.Light.Ends.callToThen (henumCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen henumCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightQueryWeights.time,
            LightSubsetEnumeration.time, hcount]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightQueryWeights.time, LightSubsetEnumeration.time, hcount] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightQueryWeights.time,
            LightSubsetEnumeration.time, hcount] <;>
          omega)
    on_goal -1 => (rintro res μ₂ ⟨hres, hout, hkept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨by simpa using hres, ?_, ?_, ?_⟩
  · simpa only [output_missingSets] using hout
  · intro i hi
    change μ₂ (work + i) = _
    rw [hkept₁ (work + i) (Or.inr (by omega))]
    exact hwtable i hi
  · intro i hi
    exact (hkept₁ i hi.2).trans (hkept₀ i ⟨by omega, Or.inl hi.1⟩)
end ThreeSum.LightQueryEnumeration

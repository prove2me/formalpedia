-- Prove2me | solution 1 for ThreeSum.LightTernaryTaggedChannel.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:18.087181+00:00
-- url     : https://prove2.me/submissions/45a28efb-9e91-4d8c-b1be-cda484be7a93

import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryProductChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryTaggedChannel
import Theorems.Thm_ThreeSum_LightTernaryTaggedChannel_offset_meets
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryProductChannel_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_involutive
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_scalarPower_eval
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryTaggedChannel
open Light TernarySignedLayout
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryTaggedChannel
theorem _root_.solution {pMain pOffset pProduct src n J a b dst U : ℕ}
    (hmain : P[pMain]? = some (body pOffset pProduct)) (hoffset : P[pOffset]? = some offsetBody)
    (hproduct : P[pProduct]? = some LightTernaryProductChannel.body) (μ : ℕ → ℤ) (F : ℕ → ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (ha : a < J + 2) (hb : b < J + 2)
    (hsrc : src + n * (J + 2) ≤ dst) (hdst : dst + n ≤ lim.space)
    (hread : ∀ i < n, ∀ j < J + 2, μ (src + i * (J + 2) + offset J j) = F i j)
    (hf : ∀ i < n, ∀ j < J + 2, |F i j| ≤ (U : ℤ)) (hword : ((U : ℤ) + 1) ^ 2 ≤ lim.word)
    (hindex : ((J + 3 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src, n, J, a, b, dst] μ (time n)
      (fun _ ν => (∀ i < n, ν (dst + i) = F i a * F i b) ∧ SameOutside μ ν dst n) :=
  by
  let G : ℕ → ℕ → ℤ := fun i j => F i (offset J j)
  have hr : ∀ i < n, ∀ j < J + 2, μ (src + i * (J + 2) + j) = G i j :=
    by
    intro i hi j hj
    have hh := hread i hi (offset J j) (offset_lt hj)
    rwa [offset_involutive hj] at hh
  have hg : ∀ i < n, ∀ j < J + 2, |G i j| ≤ (U : ℤ) :=
    by
    intro i hi j hj
    exact hf i hi (offset J j) (offset_lt hj)
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
    first
    | refine _root_.Light.Ends.callToThen ((offset_meets (d := d + 1) hoffset μ ha hindex) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (offset_meets (d := d + 1) hoffset μ ha hindex) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryProductChannel.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryProductChannel.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryProductChannel.time] <;> omega)
    on_goal -1 => (rintro ra ν ⟨hra, hma⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
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
    | refine _root_.Light.Ends.callToThen ((offset_meets (d := d + 1) hoffset μ hb hindex) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (offset_meets (d := d + 1) hoffset μ hb hindex) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryProductChannel.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryProductChannel.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryProductChannel.time] <;> omega)
    on_goal -1 => (rintro rb ν ⟨hrb, hmb⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightTernaryProductChannel.meets (d := d + 1) (a := offset J a) (b := offset J b) (width := J + 2) hproduct
              μ G hw (offset_lt ha) (offset_lt hb) hsrc hdst hr hg hword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightTernaryProductChannel.meets (d := d + 1) (a := offset J a) (b := offset J b) (width := J + 2) hproduct μ
            G hw (offset_lt ha) (offset_lt hb) hsrc hdst hr hg hword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hra, hrb, LightTernaryProductChannel.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hra, hrb, LightTernaryProductChannel.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hra, hrb, LightTernaryProductChannel.time] <;> omega)
    on_goal -1 => (rintro r ξ ⟨hweights, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, hkeep⟩
  intro i hi
  have hh := hweights i hi
  simpa only [G, offset_involutive ha, offset_involutive hb] using hh
end ThreeSum.LightTernaryTaggedChannel

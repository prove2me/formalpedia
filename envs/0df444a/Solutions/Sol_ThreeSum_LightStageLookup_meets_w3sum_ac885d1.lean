-- Prove2me | solution 1 for ThreeSum.LightStageLookup.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:36.707005+00:00
-- url     : https://prove2.me/submissions/24b00fb3-48f1-46c3-812b-f28e092d1831

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Definitions.Def_Submission_ThreeSum_LightStageLookup
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
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
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
open ThreeSum ThreeSum.LightStageLookup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightStageLookup
theorem _root_.solution {pMain pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pSize pAddress)) (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) {μ : ℕ → ℤ} {L cut base j work d : ℕ} (S : Finset (Fin L))
    (value : ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L) (hdata : base + (L + 1) * downsetCap L cut ≤ work)
    (hspace : work + tableSize L + (L + 1) ≤ lim.space) (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ cut) (hj : j ≤ L) (hread : μ (readAddr cut base j S) = value) (hd : d + L + 5 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, S.card, subsetMask S, j, base, work] μ (time L)
      (fun r μ' => r = value ∧ Kept μ μ' work) :=
  by
  have hr := subsetRank_lt hS
  have hmul := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hj)
  have haddr : readAddr cut base j S < work := by
    unfold readAddr
    simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul] at hmul hdata
    omega
  have hindex : j * downsetCap L cut ≤ readAddr cut base j S := by unfold readAddr; omega
  apply Meets.of_body hmain
  unfold body time
  have hs := LightDownsetSize.meets (d := d + 1) (μ := μ) hSize C hOffset hw hspace hword hcut (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetSize.time,
            LightDownsetAddress.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetSize.time, LightDownsetAddress.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightDownsetSize.time,
            LightDownsetAddress.time] <;> omega)
    on_goal -1 => (rintro cap μ₁ ⟨hcap, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have ha :=
    LightDownsetAddress.meets (d := d + 1) (μ := μ₁) hAddress C hOffset hw hspace hword (subsetMask_isMask S) (by omega)
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
    | refine _root_.Light.Ends.callToThen (ha _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen ha ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetSize.time,
            LightDownsetAddress.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetSize.time, LightDownsetAddress.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightDownsetSize.time,
            LightDownsetAddress.time] <;> omega)
    on_goal -1 => (rintro rank μ₂ ⟨hrank, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hrankS : rank = (subsetRank S : ℤ) := hrank
  have hread₂ : μ₂ (readAddr cut base j S) = value := (hkeep₂ _ haddr).trans ((hkeep₁ _ haddr).trans hread)
  have haddrZ : ((base : ℤ) + (j : ℤ) * (downsetCap L cut : ℤ) + (subsetRank S : ℤ)).toNat = readAddr cut base j S :=
    by
    have hh : (base : ℤ) + (j : ℤ) * (downsetCap L cut : ℤ) + (subsetRank S : ℤ) = (readAddr cut base j S : ℤ) := by
      simp [readAddr]
    rw [hh, Int.toNat_natCast]
  have hreadZ : μ₂ (((base : ℤ) + (j : ℤ) * (downsetCap L cut : ℤ) + (subsetRank S : ℤ)).toNat) = value := by
    rw [haddrZ, hread₂]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen value ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcap, hrankS, hreadZ, readAddr,
            LightDownsetSize.time, LightDownsetAddress.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcap, hrankS, hreadZ, readAddr, LightDownsetSize.time, LightDownsetAddress.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcap, hrankS, hreadZ, readAddr,
            LightDownsetSize.time, LightDownsetAddress.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨by simp, hkeep₁.trans hkeep₂⟩
end ThreeSum.LightStageLookup

-- Prove2me | solution 1 for ThreeSum.LightBoxStages.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:31.932196+00:00
-- url     : https://prove2.me/submissions/476bdf42-b7ad-4fc0-bf20-354e89ff9b03

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Theorems.Thm_Light_Meets_of_body
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
import Definitions.Def_WeightedCache3SUM_Alias_ed0b475cc4fc86b4
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_succ
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
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
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Definitions.Def_WeightedCache3SUM_Alias_8b6c5b6059fc82de
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_succ
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
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxStages
theorem _root_.solution
    {pMain pSize pPass pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pSize pPass)) (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hPass : P[pPass]? = some (LightZetaPass.body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base maskBase work U d : ℕ} (f : Finset (Fin L) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdata : base + (L + 1) * downsetCap L cut ≤ maskBase)
    (hmasks : maskBase + downsetCap L cut ≤ work) (hspace : work + tableSize L + (L + 1) ≤ lim.space)
    (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hvalueWord : ((2 ^ L * U : ℕ) : ℤ) ≤ lim.word)
    (hread : TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U) (hd : d + L + 7 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, base, maskBase, work] μ (time L cut)
      (fun _ μ' => StoredThrough μ' base cut f L ∧ KeptBut μ μ' maskBase base ((L + 1) * downsetCap L cut)) :=
  by
  have hstage (i : ℕ) (hi : i ≤ L) : stageBase base (downsetCap L cut) i + downsetCap L cut ≤ maskBase :=
    by
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hi)
    unfold stageBase
    simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul] at hm hdata
    omega
  have hfirst := hstage 0 (by omega)
  simp only [stageBase, Nat.zero_mul, Nat.add_zero] at hfirst
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetSize.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetSize.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightDownsetSize.time] <;> omega)
    on_goal -1 => (rintro cap μ₁ ⟨hcap, hsizeKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst cap
  refine
    Ends.for (Inv μ cut base maskBase work f) L (LightZetaPass.time L cut + 50) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightDownsetSize.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightDownsetSize.time] <;> first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ₁, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(L : ℤ), cut, base, maskBase, work, downsetCap L cut, 0] =
          frame ([(L : ℤ), cut, base, maskBase, work, downsetCap L cut, 0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro i hi
      have he : i = 0 := by omega
      subst i
      intro S hS
      have hr := subsetRank_lt hS
      simpa only [stageBase, Nat.zero_mul, Nat.add_zero, stageValue_zero] using
        (hsizeKept _ (by omega)).trans (hread S hS)
    · intro i hi
      exact hsizeKept i (by omega)
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hstored, hkept⟩
    have hsource := hstored j le_rfl
    have hsrc := hstage j (by omega)
    have hdst := hstage (j + 1) (by omega)
    have hsep :
      Apart (stageBase base (downsetCap L cut) j) (downsetCap L cut) (stageBase base (downsetCap L cut) (j + 1))
        (downsetCap L cut) :=
      by
      left
      simp [stageBase, Nat.add_mul, Nat.add_assoc]
    have hcurrentValues := stageValue_abs_le f hvalues j (Nat.le_of_lt hj)
    have hvalue : 2 * (((2 ^ j * U : ℕ) : ℤ)) ≤ lim.word :=
      by
      have hp : (2 ^ (j + 1) : ℕ) ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
      have hu := Nat.mul_le_mul_right U hp
      have he : 2 * (2 ^ j * U) = 2 ^ (j + 1) * U := by rw [pow_succ]; ring
      have hh : (2 * (2 ^ j * U) : ℕ) ≤ 2 ^ L * U := by rw [he]; exact hu
      exact (by exact_mod_cast hh : 2 * (((2 ^ j * U : ℕ) : ℤ)) ≤ ((2 ^ L * U : ℕ) : ℤ)).trans hvalueWord
    have hc :=
      LightZetaPass.meets (d := d + 1) hPass hEnumSetup hEnum hBatch hCell C hOffset hErase (nextCoord j hj)
        (stageValue f j) hw hcut hsrc hdst hmasks hsep hspace hword hvalue hsource hcurrentValues (by omega)
    have hsrcCast : (base : ℤ) + (j : ℤ) * (downsetCap L cut : ℤ) = (stageBase base (downsetCap L cut) j : ℤ) := by
      simp [stageBase]
    have hdstCast :
      (base : ℤ) + ((j : ℤ) + 1) * (downsetCap L cut : ℤ) = (stageBase base (downsetCap L cut) (j + 1) : ℤ) := by
      simp [stageBase]
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, nextCoord, hsrcCast,
              hdstCast]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [nextCoord, hsrcCast, hdstCast] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, nextCoord, hsrcCast, hdstCast] <;> omega)
      on_goal -1 => (rintro res μ₂ ⟨hnew, hpassKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, res, μ₂, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases heq : i = j + 1
      · subst i
        simpa only [stageValue_succ f hj] using hnew
      · have hij : i ≤ j := by omega
        have himul := Nat.mul_le_mul_right (downsetCap L cut) hij
        intro S hS
        have hr := subsetRank_lt hS
        have hbefore : stageBase base (downsetCap L cut) i + subsetRank S < stageBase base (downsetCap L cut) (j + 1) :=
          by
          unfold stageBase
          simp only [Nat.add_mul, Nat.one_mul]
          omega
        have hiend := hstage i (by omega)
        exact (hpassKept _ ⟨by omega, Or.inl hbefore⟩).trans (hstored i hij S hS)
    · intro i hi
      have hnextLow : base ≤ stageBase base (downsetCap L cut) (j + 1) :=
        by
        unfold stageBase
        omega
      have hnextHigh := hstage (j + 1) (by omega)
      have hmul := Nat.mul_le_mul_right (downsetCap L cut) (show j + 2 ≤ L + 1 by omega)
      have hnextEnd :
        stageBase base (downsetCap L cut) (j + 1) + downsetCap L cut ≤ base + (L + 1) * downsetCap L cut :=
        by
        unfold stageBase
        simp only [Nat.add_mul, Nat.one_mul] at hmul ⊢
        omega
      exact (hpassKept i ⟨hi.1, by omega⟩).trans (hkept i hi)
  case done =>
    rintro _ _ ⟨r, μ', rfl, hstored, hkept⟩
    exact ⟨hstored, hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightBoxStages

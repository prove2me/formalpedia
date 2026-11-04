-- Prove2me | solution 1 for ThreeSum.LightZetaPass.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:51.299119+00:00
-- url     : https://prove2.me/submissions/97951471-4fc8-4553-9105-708908f0129c

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Theorems.Thm_ThreeSum_LightZetaPass_choose_le_cap
import Theorems.Thm_Light_Meets_mono_time
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
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_values_layer
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_length
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateLayer
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaPass
theorem _root_.solution
    {pMain pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ} (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L) (hsrc : src + downsetCap L cut ≤ maskBase)
    (hdst : dst + downsetCap L cut ≤ maskBase) (hmasks : maskBase + downsetCap L cut ≤ work)
    (hsep : Apart src (downsetCap L cut) dst (downsetCap L cut)) (hspace : work + tableSize L + (L + 1) ≤ lim.space)
    (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hvalueWord : 2 * (U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U) (hd : d + L + 6 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, a.val, src, dst, maskBase, work] μ (time L cut)
      (fun _ μ' => TableAt μ' dst cut (Subset.zetaStep a f) ∧ KeptBut μ μ' maskBase dst (downsetCap L cut)) :=
  by
  have hword₀ : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ (L + 1) : ℕ) ≤ (L + 1) * 2 ^ (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ cut src dst maskBase work a f) (cut + 1) (roundBudget L cut) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, μ, ?_, SameOn.refl, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(L : ℤ), cut, a.val, src, dst, maskBase, work, 0] =
          frame ([(L : ℤ), cut, a.val, src, dst, maskBase, work, 0] ++ [0, 0])
      exact (frame_append_zeros _ 2).symm
    · intro S hS
      simp [stageValues]
  case round =>
    rintro j _ hj _ ⟨n, r, μ', rfl, hkept, hout⟩
    have hjcut : j ≤ cut := by omega
    have hchoose := choose_le_cap hcut hjcut
    have hsource : TableAt μ' src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (hkept _ ⟨by omega, by omega⟩).trans (hread T hT)
    have hen :=
      LightSubsetEnumerationSetup.meets (d := d + 1) hEnumSetup C.powers hEnum (μ := μ') (L := L) (k := j) (dst :=
        maskBase) (work := work) hw (by omega) hword₀ (by omega) (by omega) (by omega)
    have hentime : LightSubsetEnumerationSetup.time L j ≤ enumBudget L cut := by
      exact
        (LightSubsetEnumerationSetup.time_bound L j).trans
          (Nat.mul_le_mul_left (800 * (L + 1)) (Nat.succ_le_succ hchoose))
    unfold roundBody roundBudget
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
      | refine _root_.Light.Ends.callToThen ((hen.mono_time hentime) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (hen.mono_time hentime) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumBudget,
              batchBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [enumBudget, batchBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumBudget, batchBudget] <;> omega)
      on_goal -1 =>
        (rintro count μ₁ ⟨hcount, hseg, hpowers, henkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hsource₁ : TableAt μ₁ src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (henkept _ ⟨by omega, Or.inl (by omega)⟩).trans (hsource T hT)
    have hb :=
      LightZetaBatch.meets (d := d + 1) hBatch hCell C hOffset hErase (enumerateLayer L j) a f hw (by omega) (by omega)
        (by rw [enumerateLayer_length]; omega) hsep (Or.inr hdst) hspace hword hvalueWord hsource₁ hvalues hseg
        (fun m hm => (mem_enumerateLayer L j m).mp hm) hjcut (by omega)
    have hbtime : LightZetaBatch.time L (enumerateLayer L j).length ≤ batchBudget L cut :=
      by
      rw [enumerateLayer_length]
      exact
        (LightZetaBatch.time_bound L (L.choose j)).trans
          (Nat.mul_le_mul_left (2100 * (L + 1) ^ 2) (Nat.succ_le_succ hchoose))
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
      | refine _root_.Light.Ends.callToThen ((hb.mono_time hbtime) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (hb.mono_time hbtime) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount,
              enumerateLayer_length, enumBudget, batchBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcount, enumerateLayer_length, enumBudget, batchBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, enumerateLayer_length, enumBudget,
              batchBudget] <;>
            omega)
      on_goal -1 => (rintro res μ₂ ⟨hnew, hbkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, count, res, μ₂, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hbkept i ⟨by omega, hi.2⟩).trans ((henkept i ⟨by omega, Or.inl hi.1⟩).trans (hkept i hi))
    · intro T hT
      have hr := subsetRank_lt hT
      have hn := hnew T hT
      rw [LightZetaBatch.values_layer] at hn
      have hbefore : μ₁ (dst + subsetRank T) = μ' (dst + subsetRank T) := henkept _ ⟨by omega, Or.inl (by omega)⟩
      by_cases heq : T.card = j
      · have hlt : T.card < j + 1 := by omega
        simpa only [stageValues, heq, ite_true, show j < j + 1 by omega] using hn
      · rw [if_neg heq, hbefore, hout T hT] at hn
        have hlt : T.card < j + 1 ↔ T.card < j := by omega
        simpa only [stageValues, hlt] using hn
  case done =>
    rintro _ _ ⟨n, r, μ', rfl, hkept, hout⟩
    refine ⟨?_, hkept⟩
    intro T hT
    simpa only [stageValues, show T.card < cut + 1 by omega, ite_true] using hout T hT
  case bound =>
    rintro j _ hj _ ⟨n, r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightZetaPass

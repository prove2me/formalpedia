-- Prove2me | solution 1 for ThreeSum.LightWeightedEnumerationSetup.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:04.278541+00:00
-- url     : https://prove2.me/submissions/11a8a00c-5b73-45b1-a1f4-91396ba5aefe

import Definitions.Def_Submission_Weighted_LightEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightCacheEnumeration_pow_two_even
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] ThreeSum.LightCacheEnumeration.output_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumerationSetup
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedEnumerationSetup
theorem _root_.solution {pMain pPowers pEnum : ℕ} (hmain : P[pMain]? = some (body pPowers pEnum))
    (hpowers : P[pPowers]? = some powTableBody) (henum : P[pEnum]? = some (LightCacheEnumeration.body pEnum))
    {μ : ℕ → ℤ} {N T dst work d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (hspace : work + (2 * N + 1) ≤ lim.space)
    (hword : ((4 ^ (N + 1) : ℕ) : ℤ) ≤ lim.word) (hcontrol : ((1025 * N + 1100 : ℕ) : ℤ) ≤ lim.word)
    (hcut : T ≤ 1025 * N) (hdst : dst + (codes N T).length ≤ work) (hd : d + N + 2 ≤ lim.depth) :
    Meets lim P pMain d [N, T, dst, work] μ (time N T)
      (fun r μ' =>
        r = ((codes N T).length : ℤ) ∧
          Seg μ' dst ((codes N T).map (fun (a : ℕ) => (a : ℤ))) ∧
            Powers μ' work (2 * N) ∧ KeptBut μ μ' work dst (codes N T).length) :=
  by
  have hbase : (2 : ℤ) ≤ lim.word :=
    by
    have hb : (2 : ℕ) ≤ 4 ^ (N + 1) := by
      have hp : 0 < (4 : ℕ) ^ N := by positivity
      rw [pow_succ]
      omega
    exact (show (2 : ℤ) ≤ ((4 ^ (N + 1) : ℕ) : ℤ) by exact_mod_cast hb).trans hword
  have hpowBound : ∀ j ≤ 2 * N + 1, ((2 ^ j : ℕ) : ℤ) ≤ lim.word :=
    by
    intro j hj
    have hle : (2 ^ j : ℕ) ≤ 4 ^ (N + 1) :=
      by
      rw [← LightCacheEnumeration.pow_two_even]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (show ((2 ^ j : ℕ) : ℤ) ≤ ((4 ^ (N + 1) : ℕ) : ℤ) by exact_mod_cast hle).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hpow := powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := 2 * N + 1) (b := 2) hpowers hw hspace hpowBound
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
    | refine _root_.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightCacheEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightCacheEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightCacheEnumeration.time] <;>
          omega)
    on_goal -1 => (rintro _ μ₁ ⟨hpowSeg, hsame₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpowSpec := powers_of_segment hpowSeg
  have hcall :=
    LightCacheEnumeration.meets (W := N) henum hw hspace hword hcontrol N T 0 dst μ₁ le_rfl hcut (by simp) hdst hpowSpec
      (d + 1) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightCacheEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightCacheEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightCacheEnumeration.time] <;>
          omega)
    on_goal -1 => (rintro res μ₂ ⟨hres, hseg, hsame₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hres, ?_, ?_, ?_⟩
  · simpa [LightCacheEnumeration.output, List.bind_eq_flatMap, ← List.map_eq_flatMap] using hseg
  · intro i hi
    change μ₂ (work + i) = _
    rw [hsame₁ (work + i) (Or.inr (by omega))]
    exact hpowSpec i hi
  · intro a ha
    exact (hsame₁ a ha.2).trans (hsame₀ a (Or.inl ha.1))
end ThreeSum.LightWeightedEnumerationSetup

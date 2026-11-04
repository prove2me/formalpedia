-- Prove2me | solution 1 for ThreeSum.LightTernaryBankCoordinate.inverse_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:10.863207+00:00
-- url     : https://prove2.me/submissions/8f521c0a-b762-48fb-b885-26e207781189

import Definitions.Def_Submission_ThreeSum_TernaryBankStageModel
import Definitions.Def_Submission_ThreeSum_LightTernaryBankCoordinate
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_values_eq_coordinateInverse
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBankStageModel_forwardStage_zero
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_one_code
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_spec
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_two_code
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_update
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_zero_code
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_lt_pow_two
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_high_lt
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_low_lt
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankCoordinate
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryBankCoordinate
theorem _root_.solution
    {N T n pMain pMeta pZero pDigit pErase pPass pCell pSearch pValue a powers L keyBase src dst d U : ℕ}
    (hmain : P[pMain]? = some (body pMeta pPass))
    (hmetaProg : P[pMeta]? = some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (hpass : P[pPass]? = some (LightTernaryInversePass.body pCell))
    (hcell : P[pCell]? = some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]? = some LightTernaryCell.inverseBody) (E : Enumeration N T n) (i : Fin N) (F : TritWord N → ℤ)
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ keyBase) (hmeta : keyBase + 4 * n ≤ powers)
    (hpows : powers + (2 * N + 1) ≤ src) (hsrc : src + n ≤ dst) (hdst : dst + n ≤ lim.space)
    (hword : ((n + 2 ^ (2 * N + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hNword : 2 * (N : ℤ) + 3 ≤ lim.word)
    (hcodes : ∀ j < n, μ (a + j) = (address (E.word j) : ℤ)) (hsource : ∀ j < n, μ (src + j) = F (E.word j))
    (hpowers : Powers μ powers (2 * N)) (hsorted : ∀ j k, j < k → k < n → address (E.word j) < address (E.word k))
    (hF : ∀ j < n, |F (E.word j)| ≤ (U : ℤ)) (hvalword : 4 * (U : ℤ) + 3 ≤ lim.word) (hL : L ≤ 2 * N) (hn : n < 2 ^ L)
    (hd : d + 2 * N + L + 4 ≤ lim.depth) :
    Meets lim P pMain d [N, low i, high i, a, n, powers, L, keyBase, src, dst] μ (time N L n)
      (fun _ μ' => (∀ j < n, μ' (dst + j) = coordinateInverse i F (E.word j)) ∧ Preserved μ μ' keyBase n dst) :=
  by
  have hwordPow : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 2 ^ (2 * N + 1) ≤ n + 2 ^ (2 * N + 1) + 16 by omega)).trans hword
  have hlow : low i ≤ 2 * N := Nat.le_of_lt (low_lt i)
  have hhigh : high i ≤ 2 * N := Nat.le_of_lt (high_lt i)
  have hc :=
    LightTernaryMetadata.meets (d := d + 1) hmetaProg hzero hdigit herase μ (fun j => address (E.word j)) hw ha hmeta
      (by omega) hwordPow hcodes hpowers (fun j _ => address_lt_pow_two _) hlow hhigh (by omega)
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
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMetadata.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMetadata.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMetadata.time] <;> omega)
    on_goal -1 => (rintro r μm ⟨hrows, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcm : ∀ j < n, μm (a + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    exact (hkeep _ (Or.inl (by omega))).trans (hcodes j hj)
  have hsm : ∀ j < n, μm (src + j) = F (E.word j) := by
    intro j hj
    exact (hkeep _ (Or.inr (by omega))).trans (hsource j hj)
  have hpm : Powers μm powers (2 * N) := by
    intro j hj
    exact (hkeep _ (Or.inr (by omega))).trans (hpowers j hj)
  have hsort : ∀ j k, j < k → k < n → (address (E.word j) : ℤ) < (address (E.word k) : ℤ) :=
    by
    intro j k hj hk
    exact_mod_cast hsorted j k hj hk
  have hmd : ∀ j < n, μm (keyBase + j) = ((E.word j i).val : ℤ) :=
    by
    intro j hj
    simpa only [digit_eq] using (hrows j hj).1
  have hm0 : ∀ j < n, μm (keyBase + n + j) = (address (E.word (index E i 0 j)) : ℤ) :=
    by
    intro j hj
    rw [index_zero_code E i j hj]
    exact (hrows j hj).2.1
  have hm1 : ∀ j < n, μm (keyBase + 2 * n + j) = (address (E.word (index E i 1 j)) : ℤ) :=
    by
    intro j hj
    rw [index_one_code E i j hj]
    exact (hrows j hj).2.2.1
  have hm2 : ∀ j < n, μm (keyBase + 3 * n + j) = (address (E.word (index E i 2 j)) : ℤ) :=
    by
    intro j hj
    rw [index_two_code E i j hj]
    exact (hrows j hj).2.2.2
  have hp :=
    LightTernaryInversePass.meets (d := d + 1) hpass hcell hsearch hvalue μm (fun j => (address (E.word j) : ℤ))
      (fun j => F (E.word j)) (fun j => E.word j i) (index E i) hw (by omega) hsrc (by omega) (by omega) hdst hword hcm
      hsm hpm hsort (fun e j hj => (index_spec E i e j hj).1) hmd hm0 hm1 hm2 hF hvalword hL hn (by omega)
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryPass.time,
            LightTernaryInversePass.time, LightTernaryMetadata.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryPass.time, LightTernaryInversePass.time, LightTernaryMetadata.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryPass.time,
            LightTernaryInversePass.time, LightTernaryMetadata.time] <;>
          omega)
    on_goal -1 => (rintro r' μ' ⟨hout, hpassKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  dsimp only
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [hout j hj]
    exact
      LightTernaryInversePass.values_eq_coordinateInverse E.word i (fun j => E.word j i) (index E i) F j rfl
        (fun e he => index_update E i e j hj he)
  · intro x hxMeta hxDst
    exact (hpassKeep x hxDst).trans (hkeep x hxMeta)
end ThreeSum.LightTernaryBankCoordinate

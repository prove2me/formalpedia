-- Prove2me | solution 1 for ThreeSum.LightWeightedBankAssembly.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:12.9637+00:00
-- url     : https://prove2.me/submissions/a01e0d2c-4097-45a4-b364-12d60d0d1fc8

import Definitions.Def_Submission_Weighted_BankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_Weighted_BankAssembly
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_product_abs
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
import Theorems.Thm_ThreeSum_LightTernaryCell_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryCell_zeta_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_zeta_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_inverse_meets
import Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_zeta_meets
import Theorems.Thm_ThreeSum_LightWeightedBankStages_forward_bound
import Theorems.Thm_ThreeSum_LightWeightedBankStages_inverse_meets
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_zeta_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
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
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace ThreeSum.LightWeightedBankAssembly
theorem _root_.solution {N T n a powers L keyBase fbase gbase hbase d V : ℕ} (E : Enumeration N T n)
    (F G : TritWord N → ℤ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ keyBase)
    (hmeta : keyBase + 4 * n ≤ powers) (hpows : powers + (2 * N + 1) ≤ fbase) (hfg : fbase + (N + 1) * n ≤ gbase)
    (hgh : gbase + (N + 1) * n ≤ hbase) (hspace : hbase + (N + 1) * n ≤ lim.space)
    (hword : ((n + 2 ^ (2 * N + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hNword : 2 * (N : ℤ) + 3 ≤ lim.word)
    (hcodes : ∀ j < n, μ (a + j) = (address (E.word j) : ℤ)) (hsourceF : ∀ j < n, μ (fbase + j) = F (E.word j))
    (hsourceG : ∀ j < n, μ (gbase + j) = G (E.word j)) (hpowers : Powers μ powers (2 * N))
    (hsorted : ∀ j k, j < k → k < n → address (E.word j) < address (E.word k)) (hF : ∀ R, |F R| ≤ (V : ℤ))
    (hG : ∀ R, |G R| ≤ (V : ℤ)) (hforwardWord : 4 * ((4 ^ N * V : ℕ) : ℤ) + 3 ≤ lim.word)
    (hproductWord : (valueBound N V : ℤ) ≤ lim.word)
    (hinverseWord : 4 * ((4 ^ N * valueBound N V : ℕ) : ℤ) + 3 ≤ lim.word) (hL : L ≤ 2 * N) (hn : n < 2 ^ L)
    (hd : d + 2 * N + L + 6 ≤ lim.depth) :
    Meets lim program 0 d [N, a, n, powers, L, keyBase, fbase, gbase, hbase] μ (time N L n)
      (fun _ μ' =>
        Stages E (fun s => forwardStage s F) fbase N μ' ∧
          Stages E (fun s => forwardStage s G) gbase N μ' ∧
            Stages E (fun s => stageValue s (product F G)) hbase N μ' ∧
              Preserved μ μ' keyBase n fbase gbase hbase N ∧ Powers μ' powers (2 * N)) :=
  by
  have hstageLength : (N + 1) * n = N * n + n := by ring
  have hfg' : fbase + N * n + n ≤ gbase := by nlinarith only [hfg]
  have hgh' : gbase + N * n + n ≤ hbase := by nlinarith only [hgh]
  have hspace' : hbase + N * n + n ≤ lim.space := by nlinarith only [hspace]
  have hfn : fbase + n ≤ gbase := by omega
  have hgn : gbase + n ≤ hbase := by omega
  have hhn : hbase + n ≤ lim.space := by omega
  have hcf :=
    LightWeightedBankStages.zeta_meets (P := program) (pMain := 1) (pCoord := 2) (pMeta := 3) (pZero := 4) (pDigit := 5)
      (pErase := 6) (pPass := 7) (pCell := 8) (pSearch := 9) (pValue := 10) (d := d + 1) rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl E F μ hw ha hmeta hpows (by omega) hword hNword hcodes hsourceF hpowers hsorted hF hforwardWord hL hn
      (by omega)
  apply Meets.of_body (show program[0]? = some body from rfl)
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
    | refine _root_.Light.Ends.callToThen (hcf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcf ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedBankSweep.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedBankSweep.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedBankSweep.time] <;> omega)
    on_goal -1 => (rintro rf μf ⟨hstF, hkeepF, hpowF⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcodesF : ∀ j < n, μf (a + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    exact (hkeepF _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodes j hj)
  have hsourceGf : ∀ j < n, μf (gbase + j) = G (E.word j) :=
    by
    intro j hj
    exact (hkeepF _ (Or.inr (by omega)) (Or.inr (by omega))).trans (hsourceG j hj)
  have hcg :=
    LightWeightedBankStages.zeta_meets (P := program) (pMain := 1) (pCoord := 2) (pMeta := 3) (pZero := 4) (pDigit := 5)
      (pErase := 6) (pPass := 7) (pCell := 8) (pSearch := 9) (pValue := 10) (d := d + 1) rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl E G μf hw ha hmeta (by omega) (by omega) hword hNword hcodesF hsourceGf hpowF hsorted hG hforwardWord hL
      hn (by omega)
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
    | refine _root_.Light.Ends.callToThen (hcg _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcg ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedBankSweep.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedBankSweep.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedBankSweep.time] <;> omega)
    on_goal -1 => (rintro rg μg ⟨hstG, hkeepG, hpowG⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hstFg : Stages E (fun s => forwardStage s F) fbase N μg :=
    by
    intro s hs j hj
    have hm := Nat.mul_le_mul_right n hs
    exact (hkeepG _ (Or.inr (by omega)) (Or.inl (by omega))).trans (hstF s hs j hj)
  have hcp :=
    LightTernaryProduct.meets (P := program) (p := 16) (d := d + 1) (a := fbase + N * n) (b := gbase + N * n) (dst :=
      hbase) (n := n) (U := 4 ^ N * V) (V := 4 ^ N * V) rfl μg hw (by omega) (by omega) hhn (Or.inr (Or.inl (by omega)))
      (Or.inr (Or.inl (by omega)))
      (fun j hj => by rw [hstFg N le_rfl j hj]; exact LightWeightedBankStages.forward_bound N le_rfl F V hF _)
      (fun j hj => by rw [hstG N le_rfl j hj]; exact LightWeightedBankStages.forward_bound N le_rfl G V hG _)
      (by simpa [valueBound, Nat.cast_mul] using hproductWord)
  have hnm : ((N : ℤ) * (n : ℤ)) ≤ lim.word :=
    by
    have : N * n ≤ lim.space := by omega
    exact (by exact_mod_cast this : (N : ℤ) * (n : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hfaddr : (fbase : ℤ) + (N : ℤ) * (n : ℤ) ≤ lim.word :=
    by
    have : fbase + N * n ≤ lim.space := by omega
    exact (by exact_mod_cast this : (fbase : ℤ) + (N : ℤ) * (n : ℤ) ≤ (lim.space : ℤ)).trans hw
  have hgaddr : (gbase : ℤ) + (N : ℤ) * (n : ℤ) ≤ lim.word :=
    by
    have : gbase + N * n ≤ lim.space := by omega
    exact (by exact_mod_cast this : (gbase : ℤ) + (N : ℤ) * (n : ℤ) ≤ (lim.space : ℤ)).trans hw
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
    | refine _root_.Light.Ends.callToThen (hcp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryProduct.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryProduct.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryProduct.time] <;> omega)
    on_goal -1 => (rintro rp μp ⟨hstP, hkeepP⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcodesP : ∀ j < n, μp (a + j) = (address (E.word j) : ℤ) :=
    by
    intro j hj
    exact (hkeepP _ (Or.inl (by omega))).trans ((hkeepG _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodesF j hj))
  have hpowP : Powers μp powers (2 * N) := by
    intro j hj
    exact (hkeepP _ (Or.inl (by omega))).trans (hpowG j hj)
  have hsourceH : ∀ j < n, μp (hbase + j) = product F G (E.word j) :=
    by
    intro j hj
    rw [hstP j hj, hstFg N le_rfl j hj, hstG N le_rfl j hj]
    rfl
  have hci :=
    LightWeightedBankStages.inverse_meets (P := program) (pMain := 11) (pCoord := 12) (pMeta := 3) (pZero := 4)
      (pDigit := 5) (pErase := 6) (pPass := 13) (pCell := 14) (pSearch := 9) (pValue := 15) (d := d + 1) rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl E (product F G) μp hw ha hmeta (by omega) hspace hword hNword hcodesP hsourceH hpowP
      hsorted (product_abs F G V hF hG) hinverseWord hL hn (by omega)
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
    | refine _root_.Light.Ends.callToThen (hci _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hci ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightWeightedBankSweep.time,
            LightTernaryProduct.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightWeightedBankSweep.time, LightTernaryProduct.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedBankSweep.time,
            LightTernaryProduct.time] <;>
          omega)
    on_goal -1 => (rintro ri μi ⟨hstH, hkeepI, hpowI⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_, hstH, ?_, hpowI⟩
  · intro s hs j hj
    have hm := Nat.mul_le_mul_right n hs
    exact
      (hkeepI _ (Or.inr (by omega)) (Or.inl (by omega))).trans ((hkeepP _ (Or.inl (by omega))).trans (hstFg s hs j hj))
  · intro s hs j hj
    have hm := Nat.mul_le_mul_right n hs
    exact
      (hkeepI _ (Or.inr (by omega)) (Or.inl (by omega))).trans ((hkeepP _ (Or.inl (by omega))).trans (hstG s hs j hj))
  · intro x hxMeta hxF hxG hxH
    have hxI : x < hbase + n ∨ hbase + (N + 1) * n ≤ x := by
      rcases hxH with h | h; exact Or.inl (by omega)
      exact Or.inr h
    have hxP : x < hbase ∨ hbase + n ≤ x := by rcases hxH with h | h; exact Or.inl h; exact Or.inr (by omega)
    exact (hkeepI x hxMeta hxI).trans ((hkeepP x hxP).trans ((hkeepG x hxMeta hxG).trans (hkeepF x hxMeta hxF)))
end ThreeSum.LightWeightedBankAssembly

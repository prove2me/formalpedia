-- Prove2me | solution 1 for ThreeSum.LightTernaryNearSource.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:40.105321+00:00
-- url     : https://prove2.me/submissions/795661f0-895e-4795-ad77-1499c05b0b66

import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSource
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
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
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSource
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightTernaryEulerMetadata
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearSource
theorem _root_.solution
    {pMain pRanks pMetadata pMemo pColumn pCell pDigit pZero pErase pRank pSearch pScan pFill pRow pSum pDivide
      pNaturalDivide N a rows powers bank nb bv L T activeBase ws rankBase vals h maxRank pcount fr U V d : ℕ}
    (hmain : P[pMain]? = some (body pRanks pMetadata pMemo))
    (hranks : P[pRanks]? = some (LightTernaryRankTable.body pRank))
    (hmetadata : P[pMetadata]? = some (LightTernaryEulerMetadata.body pColumn))
    (hmemo : P[pMemo]? = some (LightTernaryEulerMemo.body pScan))
    (hcolumn : P[pColumn]? = some (LightTernaryPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]? = some (LightTernaryPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (hrank : P[pRank]? = some (LightTernaryRank.body pDigit))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hscan : P[pScan]? = some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]? = some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]? = some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]? = some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]? = some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]? = some LightOutputDecodeDivide.body) (μ : ℕ → ℤ) (codes bankCodes active : ℕ → ℕ)
    (bi ni : ℕ → ℕ → ℕ) (g f : ℕ → ℤ)
    (F : ∀ current, T < current → current ≤ maxRank → Light.Emod.Pre lim (current - h) V fr)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + rows ≤ ws) (hb : bank + nb ≤ ws) (hp : powers + (2 * N + 1) ≤ ws)
    (hactiveSpace : activeBase + N ≤ ws) (hbankVals : bv + nb ≤ ws) (hmetadataRanks : ws + 2 * N * rows + N ≤ rankBase)
    (hrankVals : rankBase + rows ≤ vals) (hvals : vals + rows ≤ fr) (hfr : fr ≤ lim.space) (hspace : pcount ≤ lim.space)
    (hword : ((nb + rows + 2 ^ (2 * N + 1) + 2 * N + 32 : ℕ) : ℤ) ≤ lim.word)
    (hcontrols : ((T + N + 32 : ℕ) : ℤ) ≤ lim.word) (hmemoWord : ((N + rows + maxRank + h + 20 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < rows, μ (a + j) = (codes j : ℤ)) (hbankRead : ∀ j < nb, μ (bank + j) = (bankCodes j : ℤ))
    (hactiveRead : ∀ i < N, μ (activeBase + i) = (active i : ℤ))
    (hbankSorted : ∀ j k, j < k → k < nb → bankCodes j < bankCodes k)
    (hnearSorted : ∀ j k, j < k → k < rows → codes j < codes k) (hpowers : Powers μ powers (2 * N))
    (hcodes : ∀ j < rows, codes j < 2 ^ (2 * N)) (hL : L ≤ 2 * N) (hnb : nb < 2 ^ L) (hnn : rows < 2 ^ L)
    (hnbpos : 0 < nb) (hactive : ∀ i < N, active i ≤ 1)
    (hbi :
      ∀ i < N,
        ∀ j < rows,
          active i ≠ 0 →
            LightTernaryPredecessor.digit N (lowAt N i) (highAt N i) (codes j) ≠ 0 →
              LightTernaryPredecessor.predRank N (lowAt N i) (highAt N i) (codes j) ≤ T →
                bi i j < nb ∧ bankCodes (bi i j) = LightTernaryPredecessor.code N (lowAt N i) (highAt N i) (codes j))
    (hni :
      ∀ i < N,
        ∀ j < rows,
          active i ≠ 0 →
            LightTernaryPredecessor.digit N (lowAt N i) (highAt N i) (codes j) ≠ 0 →
              T < LightTernaryPredecessor.predRank N (lowAt N i) (highAt N i) (codes j) →
                ni i j < rows ∧ codes (ni i j) = LightTernaryPredecessor.code N (lowAt N i) (highAt N i) (codes j))
    (hT : T ≤ maxRank) (hh : h ≤ T) (hrankRange : ∀ j < rows, T < ranks N codes j ∧ ranks N codes j ≤ maxRank)
    (hrange :
      ∀ j < rows,
        ∀ i < N,
          keys N rows T bv vals codes active bi ni j i < pcount ∧ keys N rows T bv vals codes active bi ni j i < fr)
    (hbank :
      ∀ j < rows,
        ∀ i < N,
          keys N rows T bv vals codes active bi ni j i < vals →
            keys N rows T bv vals codes active bi ni j i < ws ∧
              μ (keys N rows T bv vals codes active bi ni j i) = g (keys N rows T bv vals codes active bi ni j i))
    (hmemoval : ∀ j < rows, g (vals + j) = f j) (hweight : ∀ j < rows, ∀ i < N, weights N codes active j i ≤ 2)
    (hvalue : ∀ j < rows, ∀ i < N, |g (keys N rows T bv vals codes active bi ni j i)| ≤ U)
    (hpre :
      ∀ j < rows,
        ∀ i < N,
          keys N rows T bv vals codes active bi ni j i < vals ∨
            ∃ k < rows, keys N rows T bv vals codes active bi ni j i = vals + k ∧ ranks N codes k < ranks N codes j)
    (hEuler :
      ∀ j < rows,
        LightTernaryWeightedSum.sum (weights N codes active j) (keys N rows T bv vals codes active bi ni j) g N =
          (ranks N codes j - h : ℕ) * f j)
    (hV : 2 * (N + 1) * U ≤ V) (hd : d + 2 * N + 7 ≤ lim.depth) :
    Meets lim P pMain d [N, a, rows, powers, bank, nb, bv, L, T, activeBase, ws, rankBase, vals, h, maxRank, pcount, fr]
      μ (time N L rows (maxRank - T) V) (fun r ν => r = 0 ∧ Kept μ ν ws ∧ ∀ j < rows, ν (vals + j) = f j) :=
  by
  have hmetaRanks : ws + 2 * (N * rows) + N ≤ rankBase := by simpa only [Nat.mul_assoc] using hmetadataRanks
  have hmetaSpan : ws + 2 * N * rows + N ≤ lim.space := by omega
  have hrSpan : rankBase + rows ≤ lim.space := by omega
  have hrCall :=
    LightTernaryRankTable.meets (d := d + 1) hranks hrank hdigit herase μ codes hw (by omega) (by omega) hrSpan
      (by omega) (by omega) hread hpowers hcodes (by omega)
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
    | refine _root_.Light.Ends.callToThen (hrCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryRankTable.time, LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> omega)
    on_goal -1 => (rintro r₁ ν ⟨hRankRead, hRankOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hν {x : ℕ} (hx : x < ws) : ν x = μ x := hRankOutside x (Or.inl (by omega))
  have hRead : ∀ j < rows, ν (a + j) = (codes j : ℤ) := by intro j hj; rw [hν (by omega), hread j hj]
  have hbRead : ∀ j < nb, ν (bank + j) = (bankCodes j : ℤ) := by intro j hj; rw [hν (by omega), hbankRead j hj]
  have haRead : ∀ i < N, ν (activeBase + i) = (active i : ℤ) := by intro i hi; rw [hν (by omega), hactiveRead i hi]
  have hPowers : Powers ν powers (2 * N) := by intro i hi; rw [hν (by omega), hpowers i hi]
  have hmCall :=
    LightTernaryEulerMetadata.meets (d := d + 1) (bv := bv) (nv := vals) hmetadata hcolumn hcell hdigit hzero herase
      hrank hsearch ν codes bankCodes codes active bi ni hw ha hb ha hp hactiveSpace hmetaSpan (by omega) (by omega)
      hword hcontrols hRead hbRead hRead haRead hbankSorted hnearSorted hPowers hcodes hL hnb hnn hnbpos hactive hbi hni
      (by omega)
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
    | refine _root_.Light.Ends.callToThen (hmCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hmCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryRankTable.time, LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> omega)
    on_goal -1 => (rintro r₂ ξ ⟨hRecords, hMetadataOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hξ {x : ℕ} (hx : x < ws) : ξ x = μ x := (hMetadataOutside x (Or.inl hx)).trans (hν hx)
  have hRanks : ∀ j < rows, ξ (rankBase + j) = (ranks N codes j : ℤ) :=
    by
    intro j hj
    rw [hMetadataOutside _ (Or.inr (by omega))]
    exact hRankRead j hj
  have hWeights : ∀ j < rows, ∀ i < N, ξ (ws + N * j + i) = (weights N codes active j i : ℤ) :=
    by
    intro j hj i hi
    exact (hRecords i hi j hj).1
  have hKeys :
    ∀ j < rows, ∀ i < N, ξ (ws + N * rows + N * j + i) = (keys N rows T bv vals codes active bi ni j i : ℤ) :=
    by
    intro j hj i hi
    simpa only [RecordAt, rowAddr, keys, Nat.mul_add, Nat.add_assoc] using (hRecords i hi j hj).2
  have hc :=
    LightTernaryEulerMemo.meets (d := d + 1) hmemo hscan hfill hrow hsum hdivide hnatural ξ (weights N codes active)
      (keys N rows T bv vals codes active bi ni) g f (ranks N codes) F hT hh (by omega) (by omega) hrankVals hvals
      hspace hRanks hrankRange hWeights hKeys hrange
      (fun j hj i hi hk => by rw [hξ (hbank j hj i hi hk).1]; exact (hbank j hj i hi hk).2) hmemoval hweight hvalue hpre
      hEuler hV (by omega) hmemoWord hw hfr
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
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryRankTable.time, LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> omega)
    on_goal -1 => (rintro r₃ η ⟨hr₃, hKept, hValues⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryRankTable.time, LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryRankTable.time,
            LightTernaryEulerMetadata.time, LightTernaryEulerMemo.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, hValues⟩
  intro x hx
  exact (hKept x (by omega)).trans (hξ hx)
end ThreeSum.LightTernaryNearSource

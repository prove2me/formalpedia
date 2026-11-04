-- Prove2me | solution 1 for ThreeSum.LightWeightedEulerMetadata.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:09.39422+00:00
-- url     : https://prove2.me/submissions/23e25bf6-deba-4511-be8a-2b7ba7775266

import Definitions.Def_Submission_Weighted_PredecessorTable
import Definitions.Def_Submission_Weighted_EulerMetadata
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_column_keeps
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_column_outside
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
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
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
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedEulerMetadata
theorem _root_.solution
    {pMain pColumn pCell pDigit pZero pErase pRank pSearch N a rows powers bank nb bv near nn nv L T activeBase ws d :
      ℕ}
    (hmain : P[pMain]? = some (body pColumn))
    (hcolumn : P[pColumn]? = some (LightWeightedPredecessorTable.body pCell pDigit))
    (hcell : P[pCell]? = some (LightWeightedPredecessor.body pDigit pZero pErase pRank pSearch))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (hrank : P[pRank]? = some (LightWeightedCost.body pDigit))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ)
    (codes bankCodes nearCodes active : ℕ → ℕ) (bi ni : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + rows ≤ ws) (hbankSpace : bank + nb ≤ ws) (hnearSpace : near + nn ≤ ws)
    (hspace : powers + (2 * N + 1) ≤ ws) (hactiveSpace : activeBase + N ≤ ws) (hws : ws + 2 * N * rows + N ≤ lim.space)
    (hbankVals : bv + nb ≤ lim.space) (hnearVals : nv + nn ≤ lim.space)
    (hword : ((nb + nn + 2 ^ (2 * N + 1) + 1025 * N + 1100 : ℕ) : ℤ) ≤ lim.word)
    (hcontrols : ((T + N + 32 : ℕ) : ℤ) ≤ lim.word) (hread : ∀ j < rows, μ (a + j) = (codes j : ℤ))
    (hbankRead : ∀ j < nb, μ (bank + j) = (bankCodes j : ℤ)) (hnearRead : ∀ j < nn, μ (near + j) = (nearCodes j : ℤ))
    (hactiveRead : ∀ i < N, μ (activeBase + i) = (active i : ℤ))
    (hbankSorted : ∀ j k, j < k → k < nb → bankCodes j < bankCodes k)
    (hnearSorted : ∀ j k, j < k → k < nn → nearCodes j < nearCodes k) (hpowers : Powers μ powers (2 * N))
    (hcodes : ∀ j < rows, codes j < 2 ^ (2 * N)) (hL : L ≤ 2 * N) (hnb : nb < 2 ^ L) (hnn : nn < 2 ^ L)
    (hnbpos : 0 < nb) (hactive : ∀ i < N, active i ≤ 1)
    (hbi :
      ∀ i < N,
        ∀ j < rows,
          active i ≠ 0 →
            digit N (lowAt N i) (highAt N i) (codes j) ≠ 0 →
              predCost N (lowAt N i) (highAt N i) (codes j) ≤ T →
                bi i j < nb ∧ bankCodes (bi i j) = code N (lowAt N i) (highAt N i) (codes j))
    (hni :
      ∀ i < N,
        ∀ j < rows,
          active i ≠ 0 →
            digit N (lowAt N i) (highAt N i) (codes j) ≠ 0 →
              T < predCost N (lowAt N i) (highAt N i) (codes j) →
                ni i j < nn ∧ nearCodes (ni i j) = code N (lowAt N i) (highAt N i) (codes j))
    (hd : d + 2 * N + 5 ≤ lim.depth) :
    Meets lim P pMain d [N, a, rows, powers, bank, nb, bv, near, nn, nv, L, T, activeBase, ws] μ (time N L rows)
      (fun _ ν =>
        (∀ i < N, ∀ j < rows, RecordAt ν N rows ws i j (codes j) T (active i) bv nv (bi i j) (ni i j)) ∧
          SameOutside μ ν ws (2 * N * rows)) :=
  by
  have hspan : ws + 2 * (N * rows) + N ≤ lim.space := by simpa only [Nat.mul_assoc] using hws
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ N a rows powers bank nb bv near nn nv L T activeBase ws codes active bi ni) N
      (LightWeightedPredecessorTable.time N L rows + 180) ?start ?round ?done ?bound (hT := by
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
    refine ⟨0, 0, 0, 0, μ, ?_, SameOn.refl, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(N : ℤ), a, rows, powers, bank, nb, bv, near, nn, nv, L, T, activeBase, ws, 0] =
          frame ([(N : ℤ), a, rows, powers, bank, nb, bv, near, nn, nv, L, T, activeBase, ws, 0] ++ [0, 0, 0, 0])
      exact (frame_append_zeros _ 4).symm
    · intro k hk
      omega
  case round =>
    rintro i _ hi _ ⟨lo, hig, act, result, ν, rfl, H, hr⟩
    have hkeep : ∀ x < ws, ν x = μ x := fun x hx => H x (Or.inl hx)
    have hRead : ∀ j < rows, ν (a + j) = (codes j : ℤ) := by intro j hj; rw [hkeep _ (by omega), hread j hj]
    have hbRead : ∀ j < nb, ν (bank + j) = (bankCodes j : ℤ) := by intro j hj; rw [hkeep _ (by omega), hbankRead j hj]
    have hnRead : ∀ j < nn, ν (near + j) = (nearCodes j : ℤ) := by intro j hj; rw [hkeep _ (by omega), hnearRead j hj]
    have haRead : ν (activeBase + i) = (active i : ℤ) := by rw [hkeep _ (by omega), hactiveRead i hi]
    have hp : Powers ν powers (2 * N) := by intro j hj; rw [hkeep _ (by omega), hpowers j hj]
    have hlow : lowAt N i < 2 * N := by unfold lowAt; omega
    have hhigh : highAt N i < 2 * N := by unfold highAt lowAt; omega
    have hloCast : 2 * ((N : ℤ) - 1 - (i : ℤ)) = (lowAt N i : ℤ) := by unfold lowAt; omega
    have hact := hactive i hi
    have hc :=
      LightWeightedPredecessorTable.meets (d := d + 1) (dst := ws + i) (stride := N) hcolumn hcell hdigit hzero herase
        hrank hsearch ν codes bankCodes nearCodes (bi i) (ni i) hw (by omega) (by omega) (by omega) (by omega)
        (by simpa only [Nat.mul_assoc] using (show ws + i + 2 * (N * rows) ≤ lim.space by omega)) hbankVals hnearVals
        hword (by omega) hRead hbRead hnRead hbankSorted hnearSorted hp hcodes (Nat.le_of_lt hlow) (Nat.le_of_lt hhigh)
        hL hnb hnn hnbpos hact (by omega) (hbi i hi) (hni i hi) (by omega)
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (lowAt N i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hloCast,
              LightWeightedPredecessorTable.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hloCast, LightWeightedPredecessorTable.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hloCast,
              LightWeightedPredecessorTable.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (highAt N i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, highAt,
              LightWeightedPredecessorTable.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [highAt, LightWeightedPredecessorTable.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, highAt,
              LightWeightedPredecessorTable.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (active i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haRead,
              LightWeightedPredecessorTable.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [haRead, LightWeightedPredecessorTable.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haRead,
              LightWeightedPredecessorTable.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightWeightedPredecessorTable.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightWeightedPredecessorTable.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightWeightedPredecessorTable.time] <;> omega)
      on_goal -1 => (rintro out ξ ⟨hrows, hapart, houtside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, (lowAt N i : ℤ), (highAt N i : ℤ), (active i : ℤ), out, ξ, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro x hx
      exact (column_outside hi hapart x hx).trans (H x hx)
    · intro k hk j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hkN : k < N := by omega
        obtain ⟨hw0, hk0⟩ := hr k hk j hj
        unfold RecordAt
        rw [column_keeps hkN hi (by omega) hapart j, column_keeps hkN hi (by omega) hapart (rows + j)]
        exact ⟨hw0, hk0⟩
      ·
        simpa [RecordAt, LightWeightedPredecessorTable.RecordAt, rowAddr, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hrows j hj
  case done =>
    rintro _ _ ⟨lo, hig, act, result, ν, rfl, H, hr⟩
    exact ⟨hr, H⟩
  case bound =>
    rintro i _ hi _ ⟨lo, hig, act, result, ν, rfl, H, hr⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightWeightedEulerMetadata

-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentChannelStep.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:21.27337+00:00
-- url     : https://prove2.me/submissions/210bf050-1976-4015-87bc-d0cd962ec17a

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_callArgs_spec
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_callArgs_cost
import Theorems.Thm_Light_Ends_callToThen
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_meets
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
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
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval
attribute [local simp] ThreeSum.LightTernaryMomentChannelStep.callArgs_cost
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannelStep
open Light TernaryWeightChannels
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentChannelStep
namespace Procs
theorem _root_.solution {k j pMain originalB nB originalC nC leftWeight rightWeight matrix count out U V hostTime : ℕ}
    {backend : List ℤ} {positions : List ℕ} (S : Procs k j positions (9 + backend.length) P pMain) (μ : ℕ → ℤ)
    (B C accum score : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hBspace : originalB + nB ≤ leftWeight) (hCspace : originalC + nC ≤ leftWeight)
    (hmatrix : matrix + k * count + count ≤ leftWeight) (hleft : leftWeight + nB ≤ rightWeight)
    (hright : rightWeight + nC ≤ lim.space) (houtBefore : leftWeight ≤ out) (hout : out + count ≤ lim.space)
    (hleftSpace : leftWeight ≤ lim.space) (hB : ∀ i < nB, μ (originalB + i) = B i)
    (hC : ∀ i < nC, μ (originalC + i) = C i) (hBabs : ∀ i < nB, |B i| ≤ (U : ℤ)) (hCabs : ∀ i < nC, |C i| ≤ (U : ℤ))
    (haccum : ∀ i < count, μ (matrix + k * count + i) = accum i)
    (hbounded : ∀ i < count, |accum i| ≤ (V : ℤ) ∧ |score i| ≤ (V : ℤ))
    (hleftWord : max (U : ℤ) (2 * ((k.choose j : ℤ) + 1) * ((U : ℤ) + 2) ^ j) ≤ lim.word)
    (hrightWord : max (U : ℤ) (2 * ((U : ℤ) + 1) ^ (k - j)) ≤ lim.word) (haddWord : 2 * (V : ℤ) ≤ lim.word)
    (hkWord : (k : ℤ) ≤ lim.word) (hpositions : ∀ a ∈ positions, 9 ≤ a ∧ a < 9 + backend.length)
    (hargsWord : ∀ z ∈ args originalB nB originalC nC leftWeight rightWeight matrix count out backend, |z| ≤ lim.word)
    (hhost :
      ∀ ν,
        Kept μ ν leftWeight →
          (∀ i < nB, ν (leftWeight + i) = (k.choose j : ℤ) * (-(B i)) ^ j) →
            (∀ i < nC, ν (rightWeight + i) = (C i) ^ (k - j)) →
              Meets lim P S.pHost (d + 1)
                (values positions (args originalB nB originalC nC leftWeight rightWeight matrix count out backend)) ν
                hostTime (fun _ ξ => Kept ν ξ leftWeight ∧ ∀ i < count, ξ (out + i) = score i)) :
    Meets lim P pMain d (args originalB nB originalC nC leftWeight rightWeight matrix count out backend) μ
      (time k j nB nC count hostTime positions.length)
      (fun r ν =>
        r = 0 ∧
          (∀ i < count, ν (matrix + k * count + i) = accum i + score i) ∧
            ∀ a < leftWeight, (a < matrix + k * count ∨ matrix + k * count + count ≤ a) → ν a = μ a) :=
  by
  let vals := args originalB nB originalC nC leftWeight rightWeight matrix count out backend
  have hleftEnd : leftWeight + nB ≤ lim.space := by omega
  have hrowEnd : matrix + k * count + count ≤ lim.space := by omega
  have hBsafe : LightArray.SourceSafe originalB leftWeight nB := Or.inr (Or.inl hBspace)
  have hCsafe : LightArray.SourceSafe originalC rightWeight nC := Or.inr (Or.inl (by omega))
  have hwordFrame (a : ℕ) (ha : a < 9 + backend.length) : |frame vals a| ≤ lim.word :=
    by
    apply hargsWord
    have hlen : vals.length = 9 + backend.length := by simp [vals, args]; omega
    change vals.getD a 0 ∈ vals
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  apply Meets.of_body S.main
  unfold body time args
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightTernaryMomentChannels.left_meets S.left μ B hw (by omega) hleftEnd hBsafe hB hBabs hleftWord) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightTernaryMomentChannels.left_meets S.left μ B hw (by omega) hleftEnd hBsafe hB hBabs hleftWord) ?_ ?_ ?_
          ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentAccumulate.time,
            frame_setLocal]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentAccumulate.time, frame_setLocal] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentAccumulate.time,
            frame_setLocal] <;>
          omega)
    on_goal -1 => (rintro rL μL ⟨hL, hkeepL⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hprefixL : Kept μ μL leftWeight := fun a ha => hkeepL a (Or.inl ha)
  have hCreadL : ∀ i < nC, μL (originalC + i) = C i := by
    intro i hi
    exact (hprefixL _ (by omega)).trans (hC i hi)
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightTernaryMomentChannels.right_meets S.right μL C hw (by omega) hright hCsafe hCreadL hCabs hrightWord) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightTernaryMomentChannels.right_meets S.right μL C hw (by omega) hright hCsafe hCreadL hCabs hrightWord) ?_
          ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentAccumulate.time,
            frame_setLocal]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentAccumulate.time, frame_setLocal] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentAccumulate.time,
            frame_setLocal] <;>
          omega)
    on_goal -1 => (rintro rR μR ⟨hR, hkeepR⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hprefixR : Kept μ μR leftWeight := by
    intro a ha
    exact (hkeepR a (Or.inl (by omega))).trans (hprefixL a ha)
  have hLreadR : ∀ i < nB, μR (leftWeight + i) = (k.choose j : ℤ) * (-(B i)) ^ j :=
    by
    intro i hi
    exact (hkeepR _ (Or.inl (by omega))).trans (hL i hi)
  have hhostArgs :
    (∀ e ∈ callArgs positions, e.Safe lim ⟨frame (setLocal (setLocal vals 0 rL) 0 rR), μR⟩) ∧
      (callArgs positions).map (·.val ⟨frame (setLocal (setLocal vals 0 rL) 0 rR), μR⟩) = values positions vals :=
    by
    apply callArgs_spec
    · intro a ha
      have hp := hpositions a ha
      simp only [frame_setLocal, show a ≠ 0 by omega, ite_false]
    · intro a ha
      exact hwordFrame a (hpositions a ha).2
  ((first
      | refine _root_.Light.Ends.seqSelf ?_
      | refine _root_.Light.Ends.skipLast ?_);
    repeat
      with_unfolding_none
        first
        | refine _root_.Light.Ends.seqAssoc ?_
        | refine _root_.Light.Ends.skipThen ?_)
  refine
    Ends.callToThen (hhost μR hprefixR hLreadR hR) ?_ (ha := hhostArgs) (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentAccumulate.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentAccumulate.time] <;>
            first
            | omega
            | (ring_nf; omega)))
  intro rH μH ⟨hkeepH, hscore⟩
  have hprefixH : Kept μ μH leftWeight := fun a ha => (hkeepH a ha).trans (hprefixR a ha)
  have haccumH : ∀ i < count, μH (matrix + k * count + i) = accum i :=
    by
    intro i hi
    exact (hprefixH _ (by omega)).trans (haccum i hi)
  have hsep : LightArray.SourceSafe out (matrix + k * count) count := Or.inr (Or.inr (by omega))
  have hmulWord : (k : ℤ) * (count : ℤ) ≤ lim.word :=
    by
    have hh : k * count ≤ lim.space := by omega
    have hh' : (k : ℤ) * (count : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast hh
    exact hh'.trans hw
  have haddr : ((matrix : ℤ) + (k : ℤ) * (count : ℤ)).toNat = matrix + k * count := by norm_cast
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightTernaryMomentAccumulate.meets S.add μH accum score hw hrowEnd hout hsep haccumH hscore hbounded
              haddWord)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightTernaryMomentAccumulate.meets S.add μH accum score hw hrowEnd hout hsep haccumH hscore hbounded
            haddWord)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr, LightTernaryMomentAccumulate.time,
            frame_setLocal]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [haddr, LightTernaryMomentAccumulate.time, frame_setLocal] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, LightTernaryMomentAccumulate.time,
            frame_setLocal] <;>
          omega)
    on_goal -1 => (rintro rA ν ⟨hrow, hkeepA⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (0 : ℤ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentAccumulate.time,
            frame_setLocal]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentAccumulate.time, frame_setLocal] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentAccumulate.time,
            frame_setLocal] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, hrow, ?_⟩
  intro a ha haway
  exact (hkeepA a haway).trans (hprefixH a ha)
end Procs
end ThreeSum.LightTernaryMomentChannelStep

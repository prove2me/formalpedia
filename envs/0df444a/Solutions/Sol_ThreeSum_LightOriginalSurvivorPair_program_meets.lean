-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivorPair.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:00.396199+00:00
-- url     : https://prove2.me/submissions/6493b5b7-eab0-46a1-840d-f717556fe287

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_Output_of_kept
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_program_length
import Theorems.Thm_ThreeSum_LightOriginalSurvivorStage_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.LightOriginalCollisionCleanup.program_length
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.selected_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightOriginalSurvivorPair
theorem _root_.solution
    {aBase nA bBase nB cBase nC keyB keyC histB histC q powers W L U d outB valueB packedB lengthB outC valueC packedC
      lengthC : ℕ}
    (μ : ℕ → ℤ) (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hA : aBase + nA ≤ outB)
    (hB : bBase + nB ≤ outB) (hC : cBase + nC ≤ outB) (hkB : keyB + nB ≤ outB) (hkC : keyC + nC ≤ outB)
    (hhB : histB + q ≤ outB) (hhC : histC + q ≤ outB) (hp : powers + (W + 1) ≤ outB) (hB1 : outB + 2 * nB ≤ valueB)
    (hB2 : valueB + nB ≤ packedB) (hB3 : packedB + nB ≤ lengthB) (hBC : lengthB + 1 ≤ outC)
    (hC1 : outC + 2 * nC ≤ valueC) (hC2 : valueC + nC ≤ packedC) (hC3 : packedC + nC ≤ lengthC)
    (hEnd : lengthC + 1 ≤ lim.space) (hword : ((nB + nC + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hkeysB : ∀ i < nB, keysB i < q) (hkeysC : ∀ i < nC, keysC i < q) (hreadKB : ∀ i < nB, μ (keyB + i) = (keysB i : ℤ))
    (hreadKC : ∀ i < nC, μ (keyC + i) = (keysC i : ℤ)) (hcountsB : ∀ k < q, μ (histB + k) = (counts keysB nB k : ℤ))
    (hcountsC : ∀ k < q, μ (histC + k) = (counts keysC nC k : ℤ)) (hboundA : ∀ i < nA, |A i| ≤ U)
    (hboundB : ∀ i < nB, |B i| ≤ U) (hboundC : ∀ i < nC, |C i| ≤ U) (hreadA : ∀ i < nA, μ (aBase + i) = A i)
    (hreadB : ∀ i < nB, μ (bBase + i) = B i) (hreadC : ∀ i < nC, μ (cBase + i) = C i)
    (hvalueWord : 2 * (U : ℤ) + 3 ≤ lim.word) (hpowers : Powers μ powers W)
    (hsortedB : ∀ i j, i < j → j < nB → B i < B j) (hsortedC : ∀ i j, i < j → j < nC → C i < C j) (hL : L ≤ W)
    (hnB : nB < 2 ^ L) (hnC : nC < 2 ^ L) (hd : d + L + 5 ≤ lim.depth) :
    Meets lim program 8 d
      [aBase, nA, bBase, nB, cBase, nC, keyB, keyC, histB, histC, q, powers, L, outB, valueB, packedB, lengthB, outC,
        valueC, packedC, lengthC]
      μ (time keysB keysC nA nB nC L)
      (fun ret ν =>
        ret =
            (if LightDeletedTwoSum.flag (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 = 0 then
              (LightDeletedTwoSum.flag (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) : ℤ)
            else 1) ∧
          Output ν keysB B nB outB valueB packedB lengthB ∧
            Output ν keysC C nC outC valueC packedC lengthC ∧
              Kept μ ν outB ∧
                LightOriginalSurvivorStage.Above μ ν lengthC ∧
                  (∀ x,
                    LightOriginalSurvivorStage.Unwritten outB nB valueB packedB (indices keysB nB).length lengthB x →
                      LightOriginalSurvivorStage.Unwritten outC nC valueC packedC (indices keysC nC).length lengthC x →
                        ν x = μ x)) :=
  by
  have hfirst :=
    (LightOriginalSurvivorStage.program_meets (d := d + 1) (W := W) (U := U) (L := L) (keyBase := keyB) (n := nB)
          (hist := histB) (q := q) (out := outB) (valuesBase := bBase) (scanBase := aBase) (scanN := nA) (targetBase :=
          cBase) (targetN := nC) (powers := powers) (dstValues := valueB) (dstKeys := packedB) (lengthCell := lengthB) 1
          μ keysB B A C hw hkB hhB hB hA hC hp hB1 hB2 hB3 (by omega) (by omega) hkeysB hreadKB hcountsB hboundB hreadB
          hboundA hreadA hreadC (by norm_num) hvalueWord hpowers hsortedC hL hnC (by omega)).append
      [body]
  apply Meets.of_body (p := 8) (by rfl : program[8]? = some body)
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
    | refine _root_.Light.Ends.callToThen (hfirst _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hfirst ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOriginalSurvivorStage.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOriginalSurvivorStage.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalSurvivorStage.time] <;> omega)
    on_goal -1 =>
      (rintro retB ν ⟨hrB, hlB, hiB, hvB, hkB, hKeepB, hAboveB, hRestB⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hOutB : Output ν keysB B nB outB valueB packedB lengthB := ⟨hlB, hiB, hvB, hkB⟩
  have hPowers : Powers ν powers W := by
    intro i hi
    rw [hKeepB _ (by omega), hpowers i hi]
  have hsecond :=
    (LightOriginalSurvivorStage.program_meets (d := d + 1) (W := W) (U := U) (L := L) (keyBase := keyC) (n := nC)
          (hist := histC) (q := q) (out := outC) (valuesBase := cBase) (scanBase := aBase) (scanN := nA) (targetBase :=
          bBase) (targetN := nB) (powers := powers) (dstValues := valueC) (dstKeys := packedC) (lengthCell := lengthC)
          (-1) ν keysC C A B hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hC1 hC2 hC3 hEnd
          (by omega) hkeysC (fun i hi => (hKeepB _ (by omega)).trans (hreadKC i hi))
          (fun k hk => (hKeepB _ (by omega)).trans (hcountsC k hk)) hboundC
          (fun i hi => (hKeepB _ (by omega)).trans (hreadC i hi)) hboundA
          (fun i hi => (hKeepB _ (by omega)).trans (hreadA i hi))
          (fun i hi => (hKeepB _ (by omega)).trans (hreadB i hi)) (by norm_num) hvalueWord hPowers hsortedB hL hnB
          (by omega)).append
      [body]
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
    | refine _root_.Light.Ends.callToThen (hsecond _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsecond ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOriginalSurvivorStage.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOriginalSurvivorStage.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalSurvivorStage.time] <;> omega)
    on_goal -1 =>
      (rintro retC ξ ⟨hrC, hlC, hiC, hvC, hkC, hKeepC, hAboveC, hRestC⟩;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hOutB' := hOutB.of_kept hKeepC (by omega) (by omega) (by omega) (by omega)
  have hOutC : Output ξ keysC C nC outC valueC packedC lengthC := ⟨hlC, hiC, hvC, hkC⟩
  have hKeep : Kept μ ξ outB := fun x hx => (hKeepC x (by omega)).trans (hKeepB x hx)
  have hAbove : LightOriginalSurvivorStage.Above μ ξ lengthC :=
    by
    intro x hx
    exact (hAboveC x hx).trans (hAboveB x (by omega))
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine
      _root_.Light.Ends.iteIffThen
        (LightDeletedTwoSum.flag (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 = 0) (fun hz => ?_)
        (fun hnz => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrB]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrB] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrB] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen retC ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨?_, hOutB', hOutC, hKeep, hAbove, fun x hxB hxC => (hRestC x hxC).trans (hRestB x hxB)⟩
    change retC = _
    simpa only [if_pos hz] using hrC
  · focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (1 : ℤ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨?_, hOutB', hOutC, hKeep, hAbove, fun x hxB hxC => (hRestC x hxC).trans (hRestB x hxB)⟩
    change (1 : ℤ) = _
    simp only [if_neg hnz]
end ThreeSum.LightOriginalSurvivorPair

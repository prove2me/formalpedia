-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.degree_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:59.176905+00:00
-- url     : https://prove2.me/submissions/15fd54f5-5dff-4d76-8531-ea7187218650

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_degreeFlag_le_one
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_degreePrefix_succ
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
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
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightArgumentTable_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorSearch_program_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientSearch_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightPairSearch_first_le
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits}
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (C : Layout) {q ctx T depth : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : depth + 8 < lim.depth) (hq : 0 < q) (hp : 1 < C.p) (hdim : 0 < C.dim) (hctx : ctx + 7 ≤ C.left)
    (hpowCtx : C.powers + (2 * C.dim + 1) ≤ ctx) (htargetCtx : C.target + 2 * C.dim ≤ ctx)
    (hleft : C.left + 2 * C.dim ≤ C.right) (hspace : C.right + 2 * C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2 * C.dim, μ (C.powers + i) = ((C.p ^ i : ℕ) : ℤ))
    (hfRead : ∀ i < 2 * C.dim, μ (C.target + i) = (f i : ℤ))
    (hword : ∀ e, 0 < e → e < C.dim → (LightExtensionFactorPredicate.word (atDegree C e) q q : ℤ) ≤ lim.word)
    (hsearchWord : ((q * q + q + ctx + 20 : ℕ) : ℤ) ≤ lim.word)
    (hcontrols : ((C.p + C.dim + q + ctx + 32 : ℕ) : ℤ) ≤ lim.word)
    (htime : ∀ e, 0 < e → e < C.dim → factorTime C q e ≤ T) :
    Meets lim program 10 depth [C.p, C.dim, q, ctx, C.powers, C.target, C.left, C.right] μ (degreeTime C.dim T)
      (fun r ν => r = (degreeFlag C q f (C.dim - 1) : ℤ) ∧ Kept μ ν ctx) :=
  by
  apply Meets.of_body (by rfl : program[10]? = some degreeBody)
  unfold degreeBody degreeTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := (C.dim - 1) * (T + 200) + 30) (Q := DegreeInv μ C q ctx f (C.dim - 1)) (DegreeInv μ C q ctx f)
        (C.dim - 1) (T + 150) ?start ?round ?done ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega))))
      ?after (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, μ, ?_, SameOn.refl⟩
    simp [update_frame_setLocal, degreeFlag]
    change
      frame [(C.p : ℤ), C.dim, q, ctx, C.powers, C.target, C.left, C.right, 1, 0] =
        frame ([(C.p : ℤ), C.dim, q, ctx, C.powers, C.target, C.left, C.right, 1, 0] ++ [0, 0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨headerResult, result, ν, rfl, H⟩
    have he : 0 < j + 1 := by omega
    have hed : j + 1 < C.dim := by omega
    have hdimCast : ((C.dim - 1 : ℕ) : ℤ) = (C.dim : ℤ) - 1 := by omega
    have hpow : ∀ i ≤ 2 * C.dim, ν (C.powers + i) = ((C.p ^ i : ℕ) : ℤ) := by
      intro i hi
      rw [H _ (by omega), hpowRead i hi]
    have hf : ∀ i < 2 * C.dim, ν (C.target + i) = (f i : ℤ) := by intro i hi; rw [H _ (by omega), hfRead i hi]
    have hh :=
      LightArgumentTable.meets (depth := depth + 1) (proc := 11) (N := 7) (P := program) rfl
        (header (atDegree C (j + 1))) (by rfl) ctx ν hw (by omega)
    have hFlag := degreeFlag_le_one C q f j
    unfold degreeRound
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
      | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, header, atDegree,
              hdimCast]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [header, atDegree, hdimCast] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, header, atDegree, hdimCast] <;> omega)
      on_goal -1 =>
        (rintro rh ξ ⟨hrh, hHeader, hHeaderOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hpow' : ∀ i ≤ 2 * C.dim, ξ (C.powers + i) = ((C.p ^ i : ℕ) : ℤ) := by
      intro i hi
      rw [hHeaderOutside _ (Or.inl (by omega)), hpow i hi]
    have hf' : ∀ i < 2 * C.dim, ξ (C.target + i) = (f i : ℤ) := by
      intro i hi
      rw [hHeaderOutside _ (Or.inl (by omega)), hf i hi]
    have hc :=
      (LightExtensionFactorSearch.program_meets (atDegree C (j + 1)) (depth := depth + 1) ξ f hw (by omega) hq hp he hed
            hHeader hctx (by dsimp [atDegree]; omega) (by dsimp [atDegree]; omega) hleft hspace hpow' hf'
            (hword (j + 1) he hed) hsearchWord).append
        tail
    have hc' := hc.mono_time (htime (j + 1) he hed)
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
      | refine _root_.Light.Ends.callToThen (hc' _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc' ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, factorTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [factorTime] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, factorTime] <;> omega)
      on_goal -1 => (rintro out η ⟨hout, hKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hKept : Kept μ η ctx := by
      intro x hx
      rw [hKeep x (by dsimp [atDegree]; omega), hHeaderOutside x (Or.inl hx), H x hx]
    have hfirstWord : ((factorFirst C q f (j + 1) : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh :=
        LightPairSearch.first_le (LightPairSearch.goodCode q (LightExtensionFactorSearch.good (atDegree C (j + 1)) f))
          (q * q)
      change factorFirst C q f (j + 1) ≤ q * q at hh
      omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine
        _root_.Light.Ends.iteIffThen ((0 : ℤ) < (factorFirst C q f (j + 1) : ℤ)) (fun hpos => ?_) (fun hnonpos => ?_) ?_
          ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout, factorFirst]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, factorFirst] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, factorFirst] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · have hne : factorFirst C q f (j + 1) ≠ 0 := by omega
      have hNext : degreeFlag C q f (j + 1) = 0 := by
        unfold degreeFlag
        rw [if_neg (fun h => hne (h j (by omega)))]
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
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, rh, out, η, ?_, hKept⟩
      simp [update_frame_setLocal, hNext]
    · have hz : factorFirst C q f (j + 1) = 0 := by omega
      have hNext : degreeFlag C q f (j + 1) = degreeFlag C q f j :=
        by
        unfold degreeFlag
        simp only [degreePrefix_succ, hz, and_true]
      refine Ends.skip ⟨by simp, rh, out, η, ?_, hKept⟩
      simp [update_frame_setLocal, hNext]
  case done => intro σ _ H; exact H
  case bound =>
    rintro j _ hj _ ⟨rh, result, ν, rfl, H⟩
    have hdimCast : ((C.dim - 1 : ℕ) : ℤ) = (C.dim : ℤ) - 1 := by omega
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdimCast] <;> omega)
  case after =>
    rintro _ ⟨rh, result, ν, rfl, H⟩
    have hf := degreeFlag_le_one C q f (C.dim - 1)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (degreeFlag C q f (C.dim - 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, H⟩
end ThreeSum.LightIrreducibleFinder

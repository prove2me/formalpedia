-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.setup_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:33:39.811901+00:00
-- url     : https://prove2.me/submissions/a537f240-d0ab-4625-b4a1-9caf62e89473

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_search_meets
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_chosen_irreducible
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightArgumentTable_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
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
open TernaryExtensionEncoding
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (C : Layout) [Fact C.p.Prime] {q ctx T depth : ℕ} (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : depth + 12 < lim.depth) (B : Budget lim C q ctx T) (hq : q = C.p ^ C.dim) :
    Meets lim program 15 depth [C.p, C.dim, q, C.powers, C.target, ctx, C.left, C.right] μ (setupTime C q T)
      (fun r ν =>
        ∃ c < q,
          r = (c + 1 : ℕ) ∧
            Irreducible (monicOfCode (p := C.p) C.dim c) ∧
              (∀ i < 2 * C.dim, ν (C.target + i) = (codeDigits (p := C.p) (c + q) i : ℤ)) ∧
                (∀ i ≤ 2 * C.dim, ν (C.powers + i) = ((C.p ^ i : ℕ) : ℤ)) ∧ Kept μ ν C.powers) :=
  by
  have hcontrols := B.controls
  have hs := B.space
  have hl := B.leftRight
  have hct := B.ctxLeft
  have htc := B.targetCtx
  have hpt := B.powersTarget
  have hdb := B.decodeWord
  unfold LightCoefficientDecode.word at hdb
  have hp := B.primeBase
  have hchosen := chosen_irreducible C B.dimpos
  rw [← hq] at hchosen
  rcases hchosen with ⟨hpos, hle, hirred⟩
  let c := chosen C q q - 1
  have hc : c < q := by dsimp [c]; omega
  have hcOne : chosen C q q = c + 1 := by dsimp [c]; omega
  have hpow :=
    powTable_meets (P := program) (d := depth + 1) (p := 14) (dst := C.powers) (L := 2 * C.dim + 1) (b := C.p) (μ := μ)
      rfl hw (by omega)
      (by
        intro j hj
        have hh := Nat.pow_le_pow_right (Nat.le_of_lt hp) hj
        exact (Int.ofNat_le.mpr hh).trans (by omega))
  apply Meets.of_body (by rfl : program[15]? = some setupBody)
  unfold setupBody setupTime
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
    | refine _root_.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro r ν ⟨hPowers, hOutside⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpows : ∀ i ≤ 2 * C.dim, ν (C.powers + i) = ((C.p ^ i : ℕ) : ℤ) :=
    by
    intro i hi
    exact (hPowers i (by simp; omega)).trans (getElem_powList (by simp; omega))
  have hscan := search_meets C (depth := depth + 1) ν hw (by omega) B hpows
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
    | refine _root_.Light.Ends.callToThen (hscan _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hscan ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro picked η ⟨hPicked, hKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpows' : ∀ i ≤ 2 * C.dim, η (C.powers + i) = ((C.p ^ i : ℕ) : ℤ) := by
    intro i hi
    rw [hKeep _ (by omega), hpows i hi]
  have hdecWord : (LightCoefficientDecode.word (2 * C.dim) C.p (c + q) 0 1 : ℤ) ≤ lim.word :=
    by
    apply le_trans _ B.decodeWord
    exact_mod_cast
      (show
        LightCoefficientDecode.word (2 * C.dim) C.p (c + q) 0 1 ≤
          LightCoefficientDecode.word (2 * C.dim) C.p (2 * q) 0 1
        by unfold LightCoefficientDecode.word; omega)
  have hdec :=
    LightCoefficientDecode.meets (d := depth + 1) (P := program) (pMain := 2) (pDigit := 3) (pDivide := 4) (W :=
      2 * C.dim) (p := C.p) (k := c + q) (powers := C.powers) (start := 0) (stride := 1) (dst := C.target) (n :=
      2 * C.dim) rfl rfl rfl hw (by omega) (by omega) (by omega) (by omega) (Or.inl B.powersTarget) hdecWord
      (by intro i hi; omega) hpows'
  have hdect :=
    hdec.mono_time
      (show LightCoefficientDecode.time (2 * C.dim) (c + q) ≤ LightCoefficientDecode.time (2 * C.dim) (2 * q) by
        unfold LightCoefficientDecode.time LightRadixDigit.time; gcongr <;> omega)
  have hPicked' : picked = (c + 1 : ℕ) := by simpa only [hcOne] using hPicked
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
    | refine _root_.Light.Ends.callToThen (hdect _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hdect ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPicked', Nat.cast_add, Nat.cast_one]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPicked', Nat.cast_add, Nat.cast_one] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPicked', Nat.cast_add, Nat.cast_one] <;> omega)
    on_goal -1 => (rintro out ξ ⟨hTarget, hOut⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (c + 1 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hPicked']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hPicked'] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hPicked'] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨c, hc, by simp, hirred, ?_, ?_, ?_⟩
  · simpa only [LightCoefficientDecode.digit, codeDigits, zero_add, one_mul] using hTarget
  · intro i hi
    change ξ (C.powers + i) = ((C.p ^ i : ℕ) : ℤ)
    rw [hOut _ (Or.inl (by omega)), hpows' i hi]
  · intro x hx
    change ξ x = μ x
    rw [hOut _ (Or.inl (by omega)), hKeep x (by omega), hOutside x (Or.inl hx)]
end ThreeSum.LightIrreducibleFinder

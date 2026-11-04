-- Prove2me | solution 1 for ThreeSum.LightPrimePool.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:20.881468+00:00
-- url     : https://prove2.me/submissions/c8b60084-6f3c-43fd-a802-e454eccb6846

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_length_le
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightPrimality_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_137b880911028d95
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimePool
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {y free : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 1 < lim.depth) (hy : 0 < y) (hspace : space free y ≤ lim.space) (hword : (word y : ℤ) ≤ lim.word) :
    Meets lim P pMain d [y, free] μ (time y)
      (fun r μ' => r = (size y : ℤ) ∧ SegN μ' free (values y) ∧ Kept μ μ' free) :=
  by
  let ct := LightPrimality.time (4 * y) (4 * y)
  have hwork : free + 3 * y ≤ lim.space := by unfold space at hspace; omega
  have hwordZ : 32 * (y : ℤ) + 16 ≤ lim.word := by exact_mod_cast hword
  have htestword : (8 * (4 * y) + 16 : ℕ) ≤ lim.word :=
    by
    have hh : 8 * (4 * y) + 16 = word y := by unfold word; ring
    rw [hh]
    exact hword
  apply Meets.of_body S.main
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
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + 3 * y) ?_ ?_ ?_
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
      (Ends.for (T := 3 * y * (ct + 100) + 20) (Q := Inv μ y free (3 * y)) (Inv μ y free) (3 * y) (ct + 80) ?_ ?_ ?_ ?_
        (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))))
      ?_ (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ct] <;> first
            | omega
            | (ring_nf; omega)))
  · refine ⟨0, 0, μ, ?_, ?_, fun _ _ => rfl⟩
    · simp [scanned, update_frame_setLocal]
    · simp [scanned, SegN]
  · rintro i _ hi _ ⟨cval, rval, ν, rfl, hseg, hkept⟩
    have hlen := prefix_length_le y i
    have hcmin : 2 ≤ y + i + 1 := by omega
    have hcmax : y + i + 1 ≤ 4 * y := by omega
    have hcword : ((y + i + 1 : ℕ) : ℤ) ≤ lim.word := by omega
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (y + i + 1) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
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
      |
        refine
          _root_.Light.Ends.callToThen
            ((S.test.meets (d := d + 1) (n := y + i + 1) (free := free + 3 * y) hw hd hcmin hcmax hspace htestword) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (S.test.meets (d := d + 1) (n := y + i + 1) (free := free + 3 * y) hw hd hcmin hcmax hspace htestword) ?_ ?_
            ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      on_goal -1 => (rintro result ν₁ ⟨hresult, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst result
    have hseg₁ : SegN ν₁ free (scanned y i) := by
      apply hseg.congr
      intro j hj
      simp only [List.length_map] at hj
      exact hkeep₁ _ (by omega)
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j (by omega)).trans (hkept j hj)
    refine
      Ends.iteLast (fun ht => ?_) (fun hf => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
        (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega)))
    · have hp : Nat.Prime (y + i + 1) := by
        by_contra hn
        simpa [LightPrimality.answer, hn] using ht
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.storeToThen (free + (scanned y i).length) (y + i + 1) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [ct] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen ((scanned y i).length + 1) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [ct] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine
        ⟨by simp, y + i + 1, LightPrimality.answer (y + i + 1),
          Function.update ν₁ (free + (scanned y i).length) ((y + i + 1 : ℕ) : ℤ), ?_, ?_, ?_⟩
      · simp [scanned, hp, update_frame_setLocal]
      · simpa only [scanned, if_pos hp] using hseg₁.snoc (y + i + 1)
      · intro j hj
        rw [Function.update_of_ne (by omega)]
        exact hkept₁ j hj
    · have hp : ¬Nat.Prime (y + i + 1) := by
        intro hp
        apply hf
        simp [LightPrimality.answer, hp]
      apply Ends.skip
      refine ⟨by simp, y + i + 1, LightPrimality.answer (y + i + 1), ν₁, ?_, ?_, hkept₁⟩
      · simp [scanned, hp, update_frame_setLocal]
      · simpa only [scanned, if_neg hp] using hseg₁
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨cval, rval, ν, rfl, hseg, hkept⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  · rintro σ ⟨cval, rval, ν, rfl, hseg, hkept⟩
    have hlen := prefix_length_le y (3 * y)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen ((scanned y (3 * y)).length) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [size, values], hseg, hkept⟩
end Procs
end ThreeSum.LightPrimePool

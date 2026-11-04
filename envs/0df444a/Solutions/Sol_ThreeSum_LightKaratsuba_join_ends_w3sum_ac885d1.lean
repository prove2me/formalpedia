-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.join_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:26.94604+00:00
-- url     : https://prove2.me/submissions/f6f1f855-1773-407f-98de-a08af3b7a666

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_LightKaratsuba_window_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_linear_update_full
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
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
import Definitions.Def_WeightedCache3SUM_Alias_a7357418fd94c5da
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}
namespace ThreeSum.LightKaratsuba
theorem _root_.solution (hLinear : P[pLinear]? = some LightArray.linearBody) (hFill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {n half a b out work U : ℕ} {r : ℤ} (hn : 0 < n) (hhalf : 2 * half = n)
    (hw : (lim.space : ℤ) ≤ lim.word) (hout : out + 2 * n ≤ work) (hwork : work + 3 * n ≤ lim.space)
    (hword : 10 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (work + i)| ≤ U ∧ |μ (work + n + i)| ≤ U ∧ |μ (work + 2 * n + i)| ≤ U) (hd : d < lim.depth) :
    Ends lim P d (joinBody pLinear pFill) ⟨frame [n, a, b, out, work, half, r], μ⟩ (joinTime n) fun σ' =>
      (∀ j < 2 * n, σ'.mem (out + j) = joined μ work n half j) ∧ KeptBut μ σ'.mem work out (2 * n) :=
  by
  unfold joinBody
  have hU : (0 : ℤ) ≤ U := Nat.cast_nonneg U
  have hcall1 :=
    LightArray.linear_bounded_meets (d := d + 1) hLinear (μ := μ) (srcA := work + 2 * n) (srcB := work) (dst :=
      work + 2 * n) (n := n) (U := U) (c := -1) hw (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (by omega))
      (by norm_num) (by omega) (fun i hi => ⟨(hvalues i hi).2.2, (hvalues i hi).1⟩)
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
    | refine _root_.Light.Ends.callToThen (hcall1 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall1 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, joinTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [joinTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, joinTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hr₁, hk₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hz01 : ∀ i < n, μ₁ (work + i) = μ (work + i) := fun i hi => hk₁ _ (by omega)
  have hz21 : ∀ i < n, μ₁ (work + n + i) = μ (work + n + i) := fun i hi => hk₁ _ (by omega)
  have hm1 : ∀ i < n, |μ₁ (work + 2 * n + i)| ≤ 2 * (U : ℤ) :=
    by
    intro i hi
    rw [hr₁ i hi]
    have hab := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have hv := hvalues i hi
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      hab.trans (by omega : |μ (work + 2 * n + i)| + |μ (work + i)| ≤ 2 * (U : ℤ))
  have hcall2 :=
    LightArray.linear_bounded_meets (d := d + 1) hLinear (μ := μ₁) (srcA := work + 2 * n) (srcB := work + n) (dst :=
      work + 2 * n) (n := n) (U := 2 * U) (c := -1) hw (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (by omega))
      (by norm_num) (by push_cast; omega)
      (fun i hi => ⟨by simpa using hm1 i hi, by rw [hz21 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
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
    | refine _root_.Light.Ends.callToThen (hcall2 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall2 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, joinTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [joinTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, joinTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₂ ⟨hr₂, hk₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hz02 : ∀ i < n, μ₂ (work + i) = μ (work + i) := fun i hi => (hk₂ _ (by omega)).trans (hz01 i hi)
  have hz22 : ∀ i < n, μ₂ (work + n + i) = μ (work + n + i) := fun i hi => (hk₂ _ (by omega)).trans (hz21 i hi)
  have hmiddle : ∀ i < n, μ₂ (work + 2 * n + i) = μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) :=
    by
    intro i hi
    rw [hr₂ i hi, hr₁ i hi, hz21 i hi]
    ring
  have hm2 : ∀ i < n, |μ₂ (work + 2 * n + i)| ≤ 3 * (U : ℤ) :=
    by
    intro i hi
    rw [hmiddle i hi]
    have h₁ := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have h₂ := abs_sub (μ (work + 2 * n + i) - μ (work + i)) (μ (work + n + i))
    have hv := hvalues i hi
    omega
  have hfill := fill_meets (d := d + 1) hFill (μ := μ₂) (dst := out) (n := 2 * n) (x := 0) hw (by omega)
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
    | refine _root_.Light.Ends.callToThen (hfill _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hfill ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, joinTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [joinTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, joinTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₃ ⟨hzeroSeg, hk₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hzero : ∀ j < 2 * n, μ₃ (out + j) = 0 := by
    intro j hj
    rw [hzeroSeg j (by simpa using hj)]
    exact List.getElem_replicate ..
  have hz03 : ∀ i < n, μ₃ (work + i) = μ (work + i) := fun i hi => (hk₃ _ (by omega)).trans (hz02 i hi)
  have hz23 : ∀ i < n, μ₃ (work + n + i) = μ (work + n + i) := fun i hi => (hk₃ _ (by omega)).trans (hz22 i hi)
  have hm3 : ∀ i < n, μ₃ (work + 2 * n + i) = μ₂ (work + 2 * n + i) := fun i hi => hk₃ _ (by omega)
  have hcall3 :=
    LightArray.linear_bounded_meets (d := d + 1) hLinear (μ := μ₃) (srcA := out) (srcB := work) (dst := out) (n := n)
      (U := U) (c := 1) hw (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by omega)
      (fun i hi => ⟨by rw [hzero i (by omega), abs_zero]; exact hU, by rw [hz03 i hi]; exact (hvalues i hi).1⟩)
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
    | refine _root_.Light.Ends.callToThen (hcall3 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall3 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, joinTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [joinTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, joinTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₄ ⟨hr₄, hk₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hfirst : ∀ j < 2 * n, μ₄ (out + j) = window (fun i => μ (work + i)) 0 n j :=
    by
    have ht :=
      linear_update_full (offset := 0) (by omega : 0 + n ≤ 2 * n) hzero hz03 (by simpa only [Nat.add_zero] using hr₄)
        (by simpa only [Nat.add_zero] using hk₄)
    simpa only [one_mul, zero_add] using ht
  have hz24 : ∀ i < n, μ₄ (work + n + i) = μ (work + n + i) := fun i hi => (hk₄ _ (by omega)).trans (hz23 i hi)
  have hm4 : ∀ i < n, μ₄ (work + 2 * n + i) = μ₂ (work + 2 * n + i) := fun i hi => (hk₄ _ (by omega)).trans (hm3 i hi)
  have hcall4 :=
    LightArray.linear_bounded_meets (d := d + 1) hLinear (μ := μ₄) (srcA := out + half) (srcB := work + 2 * n) (dst :=
      out + half) (n := n) (U := 3 * U) (c := 1) hw (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (by omega))
      (by norm_num) (by push_cast; omega)
      (fun i hi =>
        ⟨by
          rw [show out + half + i = out + (half + i) by omega, hfirst _ (by omega)]
          have ht := window_bound (offset := 0) (j := half + i) (fun j hj => (hvalues j hj).1)
          push_cast; omega, by rw [hm4 i hi]; simpa using hm2 i hi⟩)
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
    | refine _root_.Light.Ends.callToThen (hcall4 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall4 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, joinTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [joinTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, joinTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₅ ⟨hr₅, hk₅⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hm4' : ∀ i < n, μ₄ (work + 2 * n + i) = μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) := fun i hi =>
    (hm4 i hi).trans (hmiddle i hi)
  have hsecond :
    ∀ j < 2 * n,
      μ₅ (out + j) =
        window (fun i => μ (work + i)) 0 n j +
          window (fun i => μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i)) half n j :=
    by
    have ht := linear_update_full (by omega : half + n ≤ 2 * n) hfirst hm4' hr₅ hk₅
    simpa only [one_mul] using ht
  have hz25 : ∀ i < n, μ₅ (work + n + i) = μ (work + n + i) := fun i hi => (hk₅ _ (by omega)).trans (hz24 i hi)
  have hcall5 :=
    LightArray.linear_bounded_meets (d := d + 1) hLinear (μ := μ₅) (srcA := out + n) (srcB := work + n) (dst := out + n)
      (n := n) (U := 4 * U) (c := 1) hw (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (by omega)) (by norm_num)
      (by push_cast; omega)
      (fun i hi =>
        ⟨by
          rw [show out + n + i = out + (n + i) by omega, hsecond _ (by omega)]
          have h₁ := window_bound (offset := 0) (j := n + i) (fun j hj => (hvalues j hj).1)
          have h₂ :
            |window (fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j)) half n (n + i)| ≤ 3 * (U : ℤ) :=
            by
            have hv :=
              window_bound (offset := half) (j := n + i) (U := 3 * U) (f := fun j =>
                μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j))
                (fun j hj => by rw [← hmiddle j hj]; simpa using hm2 j hj)
            simpa using hv
          have hs :=
            abs_add_le (window (fun j => μ (work + j)) 0 n (n + i))
              (window (fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j)) half n (n + i))
          push_cast; omega, by rw [hz25 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
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
    | refine _root_.Light.Ends.callToThen (hcall5 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall5 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, joinTime, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [joinTime, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, joinTime, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₆ ⟨hr₆, hk₆⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  constructor
  · have ht := linear_update_full (by omega : n + n ≤ 2 * n) hsecond hz25 hr₆ hk₆
    simpa only [one_mul, joined] using ht
  · intro j hj
    change μ₆ j = μ j
    rw [hk₆ j (by omega), hk₅ j (by omega), hk₄ j (by omega), hk₃ j hj.2, hk₂ j (by omega), hk₁ j (by omega)]
end ThreeSum.LightKaratsuba

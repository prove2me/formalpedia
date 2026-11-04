-- Prove2me | solution 1 for ThreeSum.LightPascal.row_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:08.134013+00:00
-- url     : https://prove2.me/submissions/df1e9cb4-ca9f-4b82-a2c2-15f2fe1e756d

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_ThreeSum_LightPascal
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_a7357418fd94c5da
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightPascal
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPascal
theorem _root_.solution {pRow pLinear : ℕ} (hrow : P[pRow]? = some (rowBody pLinear))
    (hlinear : P[pLinear]? = some LightArray.linearBody) {μ : ℕ → ℤ} {src dst L i : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d < lim.depth) (hsrc : src + (L + 1) ≤ lim.space) (hdst : dst + (L + 1) ≤ lim.space)
    (hsep : Apart src (L + 1) dst (L + 1)) (hi : i ≤ L) (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hvalues : ∀ j ≤ L, μ (src + j) = (i.choose j : ℤ)) :
    Meets lim P pRow d [src, dst, L] μ (rowTime L) fun _ μ' =>
      (∀ j ≤ L, μ' (dst + j) = ((i + 1).choose j : ℤ)) ∧ SameOutside μ μ' dst (L + 1) :=
  by
  have hb (j : ℕ) : i.choose j ≤ 2 ^ L := (Nat.choose_le_two_pow i j).trans (Nat.pow_le_pow_right (by decide) hi)
  have hbound (j : ℕ) (hj : j ≤ L) : |μ (src + j)| ≤ ((2 ^ L : ℕ) : ℤ) :=
    by
    rw [hvalues j hj, abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast hb j
  have htwice : 2 * ((2 ^ L : ℕ) : ℤ) ≤ lim.word := by
    simpa only [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hword
  have hcall :=
    LightArray.linear_bounded_meets (d := d + 1) (μ := μ) (srcA := src) (srcB := src + 1) (dst := dst + 1) (n := L)
      (U := 2 ^ L) (c := 1) hlinear hw (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (by norm_num) htwice
      (by
        intro j hj
        refine ⟨hbound j (by omega), ?_⟩
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbound (j + 1) (by omega))
  apply Meets.of_body hrow
  unfold rowBody rowTime
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
    | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hadded, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen dst 1 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightArray.linearTime] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨?_, ?_⟩
  · intro j hj
    cases j with
    | zero => simp
    | succ j =>
      change Function.update μ₁ dst 1 (dst + (j + 1)) = _
      rw [Function.update_of_ne (by omega)]
      have hjL : j < L := by omega
      have hh := hadded j hjL
      rw [hvalues j (by omega), show src + 1 + j = src + (j + 1) by omega, hvalues (j + 1) (by omega), one_mul] at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1 j, Nat.choose_succ_succ, Nat.cast_add] using hh
  · intro a ha
    change Function.update μ₁ dst 1 a = _
    rw [Function.update_of_ne (by omega)]
    exact hkept a (by omega)
end ThreeSum.LightPascal

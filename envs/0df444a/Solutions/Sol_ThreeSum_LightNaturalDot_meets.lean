-- Prove2me | solution 1 for ThreeSum.LightNaturalDot.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:27:43.643408+00:00
-- url     : https://prove2.me/submissions/2881eda3-cc72-48fa-aa81-1aa02c1651a5

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Theorems.Thm_ThreeSum_LightNaturalDot_dot_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_setLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_le
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_succ
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightNaturalDot
theorem _root_.solution {proc srcA srcB n U V : ℕ} (hp : P[proc]? = some body) (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ)) (hreadB : ∀ i < n, μ (srcB + i) = (g i : ℤ)) (hf : ∀ i < n, f i ≤ U)
    (hg : ∀ i < n, g i ≤ V) (hword : (((n + 1) * (U + 1) * (V + 1) + 10 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [srcA, srcB, n] μ (time n) (fun r ν => r = (dot f g n : ℤ) ∧ ν = μ) :=
  by
  have hprod : U * V ≤ (U + 1) * (V + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hsum : n * (U * V) ≤ (n + 1) * (U + 1) * (V + 1) + 10 :=
    by
    have hh := Nat.mul_le_mul (show n ≤ n + 1 by omega) hprod
    simpa only [Nat.mul_assoc] using hh.trans (Nat.le_add_right _ 10)
  have hbudget (z : ℕ) (hz : z ≤ (n + 1) * (U + 1) * (V + 1) + 10) : (z : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hfit (j : ℕ) (hj : j ≤ n) : (dot f g j : ℤ) ≤ lim.word :=
    hbudget _ ((dot_le f g hf hg hj).trans ((Nat.mul_le_mul_right (U * V) hj).trans hsum))
  apply Meets.of_body hp
  unfold body LightBooleanDot.body time LightBooleanDot.time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := 32 * n + 6) (Q := fun σ => σ = ⟨frame [srcA, srcB, n, dot f g n, n], μ⟩)
        (fun j σ => σ = ⟨frame [srcA, srcB, n, dot f g j, j], μ⟩) n 24 ?start ?round ?done ?bound (hT := by
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
              | (ring_nf; omega))))
      ?finish
  case start => simp [LightBooleanDot.dot_zero, update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have ha := hreadA j hj
    have hb := hreadB j hj
    have hmul : f j * g j ≤ n * (U * V) := by
      exact (Nat.mul_le_mul (hf j hj) (hg j hj)).trans (Nat.le_mul_of_pos_left _ (by omega))
    have hmulWord : ((f j * g j : ℕ) : ℤ) ≤ lim.word := hbudget _ (hmul.trans hsum)
    have hs0 := hfit j (by omega)
    have hs1 := hfit (j + 1) (by omega)
    have hsCast : (dot f g j : ℤ) + (f j : ℤ) * (g j : ℤ) = (dot f g (j + 1) : ℤ) := by simp [LightBooleanDot.dot_succ]
    unfold LightBooleanDot.loopBody
    refine
      Ends.setLast ?_ (hs := by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ha, hb, hsCast] <;> omega)) (hT := by
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
              | (ring_nf; omega)))
    simp [ha, hb, hsCast, update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound =>
    rintro j _ hj _ rfl
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    intro σ hshape
    rw [hshape]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (dot f g n : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl, rfl⟩
end ThreeSum.LightNaturalDot

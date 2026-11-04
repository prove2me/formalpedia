-- Prove2me | solution 1 for ThreeSum.LightBooleanDot.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:27.762048+00:00
-- url     : https://prove2.me/submissions/14903134-146f-4b9e-a55c-70e95f31d2b9

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_zero
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_succ
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_setLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBooleanDot
theorem _root_.solution {p : ℕ} (hp : P[p]? = some body) {μ : ℕ → ℤ} {srcA srcB n : ℕ} (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ)) (hreadB : ∀ i < n, μ (srcB + i) = (g i : ℤ)) (hf : ∀ i < n, f i ≤ 1)
    (hg : ∀ i < n, g i ≤ 1) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P p d [srcA, srcB, n] μ (time n) (fun r μ' => r = (dot f g n : ℤ) ∧ μ' = μ) :=
  by
  apply Meets.of_body hp
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
      (Ends.for (T := 32 * n + 6) (Q := fun σ => σ = ⟨frame [(srcA : ℤ), srcB, n, dot f g n, n], μ⟩)
        (fun j σ => σ = ⟨frame [(srcA : ℤ), srcB, n, dot f g j, j], μ⟩) n 24 ?_ ?_ ?_ ?_ (hT := by
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
      ?_
  · simp [dot_zero, update_frame_setLocal]
  · rintro j _ hj _ rfl
    have ha := hreadA j hj
    have hb := hreadB j hj
    have hf' := hf j hj
    have hg' := hg j hj
    have hm : f j * g j ≤ 1 := (Nat.mul_le_mul hf' hg').trans (by decide)
    have hmZ : (f j : ℤ) * g j ≤ 1 := by exact_mod_cast hm
    have hn : (0 : ℤ) ≤ (f j : ℤ) * g j := by positivity
    have hs := dot_le f g hf hg (j := j + 1) (by omega)
    have hsZ : (dot f g (j + 1) : ℤ) ≤ lim.word :=
      by
      have hsn : dot f g (j + 1) ≤ lim.space := by omega
      exact (by exact_mod_cast hsn : (dot f g (j + 1) : ℤ) ≤ lim.space).trans hw
    have hsCast : (dot f g j : ℤ) + (f j : ℤ) * g j = dot f g (j + 1) := by simp [dot_succ]
    unfold loopBody
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
  · intro σ hcounter hshape
    exact hshape
  · rintro j _ hj _ rfl
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  · intro σ hshape
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
      refine _root_.Light.Ends.setToThen (dot f g n) ?_ ?_ ?_
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
end ThreeSum.LightBooleanDot

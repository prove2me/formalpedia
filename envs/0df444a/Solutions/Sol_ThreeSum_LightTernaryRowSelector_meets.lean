-- Prove2me | solution 1 for ThreeSum.LightTernaryRowSelector.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:32:24.433518+00:00
-- url     : https://prove2.me/submissions/65a86112-a822-4b58-b87c-348307208c59

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
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
open ThreeSum ThreeSum.LightTernaryRowSelector
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryRowSelector
theorem _root_.solution {p flagBase a₀ a₁ a₂ n U d₀ d₁ d₂ t₀ t₁ t₂ : ℕ} (hprog : P[p]? = some body) (μ : ℕ → ℤ)
    (flag f₀ f₁ f₂ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hflagSpace : flagBase + n ≤ lim.space)
    (h₀ : a₀ + n ≤ lim.space) (h₁ : a₁ + n ≤ lim.space) (h₂ : a₂ + n ≤ lim.space)
    (hflag : ∀ i < n, μ (flagBase + i) = flag i ∧ |flag i| ≤ 1) (hread₀ : ∀ i < n, μ (a₀ + i) = f₀ i ∧ |f₀ i| ≤ U)
    (hread₁ : ∀ i < n, μ (a₁ + i) = f₁ i ∧ |f₁ i| ≤ U) (hread₂ : ∀ i < n, μ (a₂ + i) = f₂ i ∧ |f₂ i| ≤ U)
    (hword : (word n U d₀ d₁ d₂ t₀ t₁ t₂ : ℤ) ≤ lim.word) :
    Meets lim P p d [flagBase, a₀, a₁, a₂, n, d₀, d₁, d₂, t₀, t₁, t₂] μ (time n)
      (fun r μ' => r = (pick (Good flag f₀ f₁ f₂ d₀ d₁ d₂ t₀ t₁ t₂) n : ℤ) ∧ μ' = μ) :=
  by
  let good := Good flag f₀ f₁ f₂ d₀ d₁ d₂ t₀ t₁ t₂
  have hbudget (x : ℕ) (hx : x ≤ word n U d₀ d₁ d₂ t₀ t₁ t₂) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hden₀ := hbudget d₀ (by unfold word; omega)
  have hden₁ := hbudget d₁ (by unfold word; omega)
  have hden₂ := hbudget d₂ (by unfold word; omega)
  have htar₀ := hbudget t₀ (by unfold word; omega)
  have htar₁ := hbudget t₁ (by unfold word; omega)
  have htar₂ := hbudget t₂ (by unfold word; omega)
  have hone := hbudget 1 (by unfold word; omega)
  have hU := hbudget U (by unfold word; nlinarith)
  have hmul₀ := hbudget (U * d₀) (by unfold word; nlinarith)
  have hmul₁ := hbudget (U * d₁) (by unfold word; nlinarith)
  have hmul₂ := hbudget (U * d₂) (by unfold word; nlinarith)
  apply Meets.of_body hprog
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
      (Ends.for (T := 140 * n + 10) (Q := fun σ =>
        σ = ⟨frame [flagBase, a₀, a₁, a₂, n, d₀, d₁, d₂, t₀, t₁, t₂, n, pick good n], μ⟩)
        (fun j σ => σ = ⟨frame [flagBase, a₀, a₁, a₂, n, d₀, d₁, d₂, t₀, t₁, t₂, j, pick good j], μ⟩) n 130 ?_ ?_ ?_ ?_
        (hT := by
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
  · simp [pick, update_frame_setLocal, frame_append_zeros]
  · rintro j _ hj _ rfl
    have hpick := pick_le good j
    have hflagj := hflag j hj
    have hr₀ := hread₀ j hj
    have hr₁ := hread₁ j hj
    have hr₂ := hread₂ j hj
    have hb₀ : |f₀ j * (d₀ : ℤ)| ≤ lim.word :=
      by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hr₀.2 (Int.natCast_nonneg _)).trans (by exact_mod_cast hmul₀)
    have hb₁ : |f₁ j * (d₁ : ℤ)| ≤ lim.word :=
      by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hr₁.2 (Int.natCast_nonneg _)).trans (by exact_mod_cast hmul₁)
    have hb₂ : |f₂ j * (d₂ : ℤ)| ≤ lim.word :=
      by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hr₂.2 (Int.natCast_nonneg _)).trans (by exact_mod_cast hmul₂)
    have ⟨hprod₀lo, hprod₀hi⟩ := abs_le.mp hb₀
    have ⟨hprod₁lo, hprod₁hi⟩ := abs_le.mp hb₁
    have ⟨hprod₂lo, hprod₂hi⟩ := abs_le.mp hb₂
    have ⟨hflaglo, hflaghi⟩ := abs_le.mp hflagj.2
    have ⟨hf₀lo, hf₀hi⟩ := abs_le.mp hr₀.2
    have ⟨hf₁lo, hf₁hi⟩ := abs_le.mp hr₁.2
    have ⟨hf₂lo, hf₂hi⟩ := abs_le.mp hr₂.2
    unfold scanBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen (flag j = 0) (fun hf => ?_) (fun hnf => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflagj, hr₀, hr₁,
              hr₂]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hflagj, hr₀, hr₁, hr₂] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagj, hr₀, hr₁, hr₂] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · apply Ends.skip
      simp [pick, good, Good, hf, update_frame_setLocal]
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen ((t₀ : ℤ) < f₀ j * d₀) (fun hc₀ => ?_) (fun hnc₀ => ?_) ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflagj, hr₀, hr₁,
                hr₂]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hflagj, hr₀, hr₁, hr₂] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagj, hr₀, hr₁, hr₂] <;> omega)
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · apply Ends.skip
        simp [pick, good, Good, not_le.mpr hc₀, update_frame_setLocal]
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.iteIffThen ((t₁ : ℤ) < f₁ j * d₁) (fun hc₁ => ?_) (fun hnc₁ => ?_) ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflagj, hr₀,
                  hr₁, hr₂]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hflagj, hr₀, hr₁, hr₂] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagj, hr₀, hr₁, hr₂] <;> omega)
          all_goals
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_
        · apply Ends.skip
          simp [pick, good, Good, not_le.mpr hc₁, update_frame_setLocal]
        · focus
            ((first
                | refine _root_.Light.Ends.seqSelf ?_
                | refine _root_.Light.Ends.skipLast ?_);
              repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_)
            refine _root_.Light.Ends.iteIffThen ((t₂ : ℤ) < f₂ j * d₂) (fun hc₂ => ?_) (fun hnc₂ => ?_) ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflagj, hr₀,
                    hr₁, hr₂]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hflagj, hr₀, hr₁, hr₂] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagj, hr₀, hr₁, hr₂] <;> omega)
            all_goals
              repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_
          · apply Ends.skip
            simp [pick, good, Good, not_le.mpr hc₂, update_frame_setLocal]
          · have hg : good j := ⟨hnf, le_of_not_gt hnc₀, le_of_not_gt hnc₁, le_of_not_gt hnc₂⟩
            focus
              ((first
                  | refine _root_.Light.Ends.seqSelf ?_
                  | refine _root_.Light.Ends.skipLast ?_);
                repeat
                  with_unfolding_none
                    first
                    | refine _root_.Light.Ends.seqAssoc ?_
                    | refine _root_.Light.Ends.skipThen ?_)
              refine _root_.Light.Ends.setToThen (j + 1 : ℕ) ?_ ?_ ?_
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
            simp [pick, hg, update_frame_setLocal]
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
      refine _root_.Light.Ends.setToThen (pick good n) ?_ ?_ ?_
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
end ThreeSum.LightTernaryRowSelector

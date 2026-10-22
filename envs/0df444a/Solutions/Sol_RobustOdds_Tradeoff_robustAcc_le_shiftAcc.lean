-- Prove2me | solution 1 for RobustOdds.Tradeoff.robustAcc_le_shiftAcc
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:00:39.83657+00:00
-- url     : https://prove2.me/submissions/54f64ac6-78bb-42f7-8c33-333694bd784b

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory RobustOdds.Tradeoff

instance instFinX1 (p y : ℝ) : IsFiniteMeasure (x1Law p y) :=
  ⟨by simp [x1Law]⟩

instance instFinCond (d : ℕ) (p η y : ℝ) : IsFiniteMeasure (condLaw d p η y) := by
  unfold condLaw
  haveI : IsFiniteMeasure (weakLaw d η y) := by unfold weakLaw; infer_instance
  exact Measure.isFiniteMeasure_map _ _

lemma shiftAdv_norm_le (d : ℕ) (η y ε : ℝ) (hη : 0 ≤ η) (hy : |y| = 1) (hε : 2 * η ≤ ε) :
    ‖(-(2 * η * y)) • (Matrix.vecCons (0 : ℝ) (fun _ : Fin d => (1 : ℝ)) : Fin (d + 1) → ℝ)‖ ≤ ε := by
  have h0 : 0 ≤ ε := by linarith
  rw [pi_norm_le_iff_of_nonneg h0]
  intro j
  have hc : |2 * η * y| ≤ 2 * η := by
    rw [abs_mul, hy, mul_one, abs_of_nonneg (by linarith)]
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa using h0
  · simp only [Pi.smul_apply, Matrix.cons_val_succ, smul_eq_mul, mul_one, Real.norm_eq_abs, abs_neg]
    linarith

theorem solution (d : ℕ) (p η ε : ℝ) (hη : 0 ≤ η) (hε : 2 * η ≤ ε)
    (f : (Fin (d + 1) → ℝ) → ℝ) :
    robustAcc d p η f ε ≤ shiftAcc d p η f := by
  unfold robustAcc shiftAcc
  have key : ∀ y : ℝ, |y| = 1 → ∀ s : ℝ, 
      {x : Fin (d + 1) → ℝ | ∀ δ : Fin (d + 1) → ℝ, ‖δ‖ ≤ ε → f (x + δ) = s} ⊆
        {x | f (shiftAdv d η y x) = s} := by
    intro y hy s x hx
    have := hx _ (shiftAdv_norm_le d η y ε hη hy hε)
    simpa [shiftAdv, sub_eq_add_neg, neg_smul] using this
  have h1 : (condLaw d p η 1 {x | ∀ δ : Fin (d + 1) → ℝ, ‖δ‖ ≤ ε → f (x + δ) = 1}).toReal ≤
      (condLaw d p η 1 {x | f (shiftAdv d η 1 x) = 1}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (key 1 (by simp) 1))
  have h2 : (condLaw d p η (-1) {x | ∀ δ : Fin (d + 1) → ℝ, ‖δ‖ ≤ ε → f (x + δ) = -1}).toReal ≤
      (condLaw d p η (-1) {x | f (shiftAdv d η (-1) x) = -1}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (key (-1) (by simp) (-1)))
  linarith

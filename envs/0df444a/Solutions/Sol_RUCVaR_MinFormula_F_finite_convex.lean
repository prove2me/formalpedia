-- Prove2me | solution 1 for RUCVaR.MinFormula.F_finite_convex
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:44:58.585218+00:00
-- url     : https://prove2.me/submissions/06a77120-d347-4db6-9b31-d280f851eb9d

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

open RUCVaR.MinFormula


/-- Proof of Theorem 10, p. 14: `F_β(x, ·)` is finite and convex. -/
theorem solution {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (hint : Integrable (f x) P)
    (β : ℝ) (hβ1 : β < 1) :
    (∀ α : ℝ, Integrable (fun y => max (f x y - α) 0) P) ∧
    ConvexOn ℝ Set.univ (Fbeta P f β x) := by
  have hi (a : ℝ) : Integrable (fun y => max (f x y - a) 0) P :=
    (hint.sub (integrable_const a)).sup (integrable_const 0)
  refine ⟨hi, convex_univ, ?_⟩
  intro a ha b hb t u ht hu htu
  simp only [smul_eq_mul]
  have hpoint (y : Fin m → ℝ) :
      max (f x y - (t * a + u * b)) 0 ≤
        t * max (f x y - a) 0 + u * max (f x y - b) 0 := by
    apply max_le
    · calc
        f x y - (t * a + u * b) = t * (f x y - a) + u * (f x y - b) := by
          nlinarith [congrArg (fun z : ℝ => z * f x y) htu]
        _ ≤ t * max (f x y - a) 0 + u * max (f x y - b) 0 :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht)
            (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
    · positivity
  have hm := integral_mono (hi (t * a + u * b))
    (((hi a).const_mul t).add ((hi b).const_mul u)) hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add ((hi a).const_mul t) ((hi b).const_mul u),
    integral_const_mul, integral_const_mul] at hm
  have hc : 0 ≤ (1 - β)⁻¹ := inv_nonneg.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left hm hc
  dsimp [Fbeta]
  nlinarith



#print axioms solution

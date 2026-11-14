-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_vertex_log_split
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:12:20.90366+00:00
-- url     : https://prove2.me/submissions/3f09a2ce-763a-4318-8083-3ed49be9d552

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution (d : ℕ) (h : Fin d → ℝ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hb : ∀ i, -1 ≤ h i ∧ h i ≤ 1) :
    let P := ∏ i, (1+θ*h i)
    let Q := ∏ i, (1-h i)
    let W := fun i => (1-h i)/(1+θ*h i)
    Real.log ((P+θ*Q)/(1+θ)) =
      (∑ i, Real.log (1+θ*h i)) + Real.log (1+θ*∏ i, W i) - Real.log (1+θ) := by
  dsimp only
  let A := fun i : Fin d => 1+θ*h i
  let P := ∏ i, A i
  let Q := ∏ i, (1-h i)
  let W := fun i => (1-h i)/A i
  have ha (i : Fin d) : 0 < A i := by
    dsimp [A]
    nlinarith [mul_nonneg hθ (show 1+h i ≥ 0 by linarith [(hb i).1])]
  have hp : 0 < P := Finset.prod_pos (fun i _ => ha i)
  have hw (i : Fin d) : 0 ≤ W i := div_nonneg (by linarith [(hb i).2]) (ha i).le
  have hprodw : 0 ≤ ∏ i, W i := Finset.prod_nonneg (fun i _ => hw i)
  have ht : 0 < 1+θ*(∏ i, W i) := by nlinarith [mul_nonneg hθ hprodw]
  have hden : 0 < 1+θ := by linarith
  have hpw : P * (∏ i, W i) = Q := by
    dsimp [W]
    rw [Finset.prod_div_distrib]
    change P * (Q / P) = Q
    field_simp
  have heq : P+θ*Q = P*(1+θ*∏ i, W i) := by rw [←hpw]; ring
  change Real.log ((P+θ*Q)/(1+θ)) =
    (∑ i, Real.log (A i)) + Real.log (1+θ*∏ i, W i) - Real.log (1+θ)
  rw [heq,Real.log_div (mul_ne_zero (ne_of_gt hp) (ne_of_gt ht)) (ne_of_gt hden),
    Real.log_mul (ne_of_gt hp) (ne_of_gt ht)]
  rw [show Real.log P = ∑ i, Real.log (A i) from Real.log_prod (fun i _ => ne_of_gt (ha i))]

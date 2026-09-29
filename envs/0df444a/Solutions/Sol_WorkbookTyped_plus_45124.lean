-- Prove2me | solution 1 for WorkbookTyped.plus_45124
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:34.711529+00:00
-- url     : https://prove2.me/submissions/46f5c73b-6391-45e9-8aea-5b706f855861

/- Source: InternLM Lean-Workbook, lean_workbook_plus_45124. Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
This is an explicit-binder repair, not an unchanged formal declaration.
Added explicit real binders (a b c d : ℝ). This makes the positive-variable and normalization hypotheses consistent and the divisions real. The old inferred-natural-number contradiction and integer division proof are rejected. A new square-based proof establishes the intended inequality. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000

private lemma cubic_term_lower (a u : ℝ) (ha : 0 ≤ a) (hu : 0 < u) : a^2-a*u/4 ≤ a^3/u := by
  apply (le_div_iff₀ hu).2
  nlinarith [mul_nonneg ha (sq_nonneg (2*a-u))]

theorem solution (a b c d : ℝ) (hx: a + b + c + d = 1) (ha: a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0): a^3 / (b + c) + b^3 / (c + d) + c^3 / (d + a) + d^3 / (a + b) ≥ 1 / 8 := by
  rcases ha with ⟨ha,hb,hc,hd⟩
  have h1 := cubic_term_lower a (b+c) ha.le (by positivity)
  have h2 := cubic_term_lower b (c+d) hb.le (by positivity)
  have h3 := cubic_term_lower c (d+a) hc.le (by positivity)
  have h4 := cubic_term_lower d (a+b) hd.le (by positivity)
  have hsq : (1 : ℝ)/4 ≤ a^2+b^2+c^2+d^2 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]
  have hcross : a*(b+c)+b*(c+d)+c*(d+a)+d*(a+b) ≤ (1 : ℝ)/2 := by
    nlinarith [sq_nonneg (a-c), sq_nonneg (b-d)]
  linarith

example : (∀ (a b c d : ℝ) (hx: a + b + c + d = 1) (ha: a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0), a^3 / (b + c) + b^3 / (c + d) + c^3 / (d + a) + d^3 / (a + b) ≥ 1 / 8) := @solution
#print axioms solution

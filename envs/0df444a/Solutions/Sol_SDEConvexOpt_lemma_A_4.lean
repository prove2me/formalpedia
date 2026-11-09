-- Prove2me | solution 1 for SDEConvexOpt.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T14:18:47.475311+00:00
-- url     : https://prove2.me/submissions/88e01205-e93f-43e2-b98a-a0436f54eb79

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

theorem solution (f : ℝ≥0 → ℝ)
    (hf : liminf (fun t => (f t : EReal)) atTop ≠ limsup (fun t => (f t : EReal)) atTop) :
    ∃ α : ℝ, liminf (fun t => (f t : EReal)) atTop < (α : EReal) ∧
      (α : EReal) < limsup (fun t => (f t : EReal)) atTop ∧
      ∀ β : ℝ, 0 < β → ∃ tk : ℕ → ℝ≥0, ∀ k : ℕ, α < f (tk k) ∧ (tk k : ℝ) + β < tk (k + 1) := by
  have hle : liminf (fun t => (f t : EReal)) atTop ≤ limsup (fun t => (f t : EReal)) atTop :=
    liminf_le_limsup
  obtain ⟨α, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_le_of_ne hle hf)
  refine ⟨α, h1, h2, fun β hβ => ?_⟩
  have hfr : ∃ᶠ t in atTop, (α : EReal) < (f t : EReal) := frequently_lt_of_lt_limsup (h := h2)
  rw [frequently_atTop] at hfr
  choose g hg1 hg2 using hfr
  let F : ℝ≥0 → ℝ≥0 := fun x => g (x + β.toNNReal + 1)
  let tk : ℕ → ℝ≥0 := fun k => F^[k] (g 0)
  refine ⟨tk, fun k => ⟨?_, ?_⟩⟩
  · cases k with
    | zero => exact EReal.coe_lt_coe_iff.mp (hg2 0)
    | succ k =>
      have hk : tk (k + 1) = g (tk k + β.toNNReal + 1) := Function.iterate_succ_apply' F k (g 0)
      rw [hk]; exact EReal.coe_lt_coe_iff.mp (hg2 _)
  · have hk : tk (k + 1) = g (tk k + β.toNNReal + 1) := Function.iterate_succ_apply' F k (g 0)
    have := hg1 (tk k + β.toNNReal + 1)
    rw [hk]
    have h3 : ((tk k + β.toNNReal + 1 : ℝ≥0) : ℝ) ≤ (g (tk k + β.toNNReal + 1) : ℝ) :=
      NNReal.coe_le_coe.mpr this
    have h4 : ((tk k + β.toNNReal + 1 : ℝ≥0) : ℝ) = ((tk k : ℝ≥0) : ℝ) + β + 1 := by
      rw [NNReal.coe_add, NNReal.coe_add, Real.coe_toNNReal _ hβ.le, NNReal.coe_one]
    linarith

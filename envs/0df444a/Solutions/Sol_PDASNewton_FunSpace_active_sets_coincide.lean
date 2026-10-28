-- Prove2me | solution 1 for PDASNewton.FunSpace.active_sets_coincide
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:34:57.921992+00:00
-- url     : https://prove2.me/submissions/52e4a220-4194-4ec3-afe3-db0c347ed902

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

open MeasureTheory
open scoped ENNReal

open PDASNewton.FunSpace in
theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 2 < q)
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (β : ℝ) (hβ : 0 < β) (C : Lp ℝ 2 μ →L[ℝ] Lp ℝ q μ)
    (hAC : ∀ y : Lp ℝ 2 μ, (A y : α → ℝ) =ᵐ[μ] fun x => C y x + β * y x)
    (f ψ : Lp ℝ 2 μ) (y lam : ℕ → Lp ℝ 2 μ) (hrun : IsRun A f ψ β y lam)
    (hinit : lam 0 = f - A (y 0)) :
    ∀ k, ∀ᵐ x ∂μ, lam k x + β * (y k x - ψ x) = f x - C (y k) x - β * ψ x := by
  intro k
  have hlam : lam k = f - A (y k) := by
    cases k with
    | zero => exact hinit
    | succ k =>
      have h := (hrun k).1
      rw [← h, add_sub_cancel_left]
  rw [hlam]
  filter_upwards [Lp.coeFn_sub f (A (y k)), hAC (y k)] with x h1 h2
  simp only [Pi.sub_apply] at h1
  rw [h1, h2]
  ring

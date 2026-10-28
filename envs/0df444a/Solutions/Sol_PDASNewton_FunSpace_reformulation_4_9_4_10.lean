-- Prove2me | solution 1 for PDASNewton.FunSpace.reformulation_4_9_4_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:14:20.350462+00:00
-- url     : https://prove2.me/submissions/9de778f6-10bd-40b6-ab80-fb2a6fe1e946

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
    (f ψ ystar lamstar : Lp ℝ 2 μ) :
    IsSolution A f ψ β ystar lamstar ↔
      ((∀ᵐ x ∂μ, β * ystar x - β * ψ x + max 0 (C ystar x - f x + β * ψ x) = 0) ∧
        ∀ᵐ x ∂μ, lamstar x = f x - C ystar x - β * ystar x) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hsum : ∀ᵐ x ∂μ, (A ystar) x + lamstar x = f x := by
      filter_upwards [Lp.coeFn_add (A ystar) lamstar] with x hx
      rw [← Pi.add_apply, ← hx, h1]
    have hl : ∀ᵐ x ∂μ, lamstar x = f x - C ystar x - β * ystar x := by
      filter_upwards [hsum, hAC ystar] with x hx1 hx2
      linarith
    refine ⟨?_, hl⟩
    filter_upwards [hl, h2] with x hx1 hx2
    rw [hx1] at hx2
    simp only [max_def] at hx2 ⊢
    split_ifs at hx2 ⊢ <;> nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · apply Lp.ext
      filter_upwards [Lp.coeFn_add (A ystar) lamstar, hAC ystar, h2] with x hx1 hx2 hx3
      rw [hx1, Pi.add_apply, hx2, hx3]
      ring
    · filter_upwards [h1, h2] with x hx1 hx2
      rw [hx2]
      simp only [max_def] at hx1 ⊢
      split_ifs at hx1 ⊢ <;> nlinarith

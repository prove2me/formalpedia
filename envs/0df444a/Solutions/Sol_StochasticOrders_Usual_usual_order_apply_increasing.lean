-- Prove2me | solution 1 for StochasticOrders.Usual.usual_order_apply_increasing
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T02:49:32.566331+00:00
-- url     : https://prove2.me/submissions/0f7aaeba-1620-4a9f-8ab1-0bbbbcca50ff

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

/-! Disproof of 1d0ae100 `StochasticOrders.Usual.usual_order_apply_increasing`.

The statement puts no finiteness (probability) assumption on `μ`, `ν`. Take both to be the
top measure `⊤` on `ℝ` (every nonempty set has measure `∞`), `X ≡ 0`, `Y = -exp`, and the
monotone step `g = 1_{[0,∞)}`. Then `μ {x < X}` and `ν {x < Y}` are both `∞` for `x < 0`
and `μ {x < X} = 0` for `x ≥ 0`, so `X ≤st Y`. But `{0 < g ∘ X} = univ` has measure `∞`
while `{0 < g ∘ Y} = ∅` (since `-exp < 0`), so `g ∘ X ≤st g ∘ Y` fails at `x = 0`. -/

set_option autoImplicit false

open MeasureTheory in
lemma dp1d0a_top_apply {α : Type} [MeasurableSpace α] {s : Set α} (hs : s.Nonempty) :
    (⊤ : Measure α) s = ⊤ := by
  rw [← Measure.coe_toOuterMeasure, Measure.toOuterMeasure_top, OuterMeasure.top_apply hs]

open MeasureTheory StochasticOrders.Usual in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) (g : ℝ → ℝ) (hg : Monotone g)
    (h : UsualOrder μ ν X Y),
    UsualOrder μ ν (g ∘ X) (g ∘ Y)) := by
  intro H
  have hg : Monotone (fun r : ℝ => if 0 ≤ r then (1:ℝ) else 0) := by
    intro a b hab
    simp only
    split_ifs with h1 h2 h2 <;> first | (exfalso; exact h2 (h1.trans hab)) | norm_num
  have h : UsualOrder (⊤ : Measure ℝ) (⊤ : Measure ℝ) (fun _ => (0:ℝ))
      (fun r => -Real.exp r) := by
    intro x
    by_cases hx : x < 0
    · have hne : {ω : ℝ | x < -Real.exp ω}.Nonempty := by
        refine ⟨Real.log (-x / 2), ?_⟩
        simp only [Set.mem_ofPred_eq]
        rw [Real.exp_log (by linarith)]
        linarith
      rw [dp1d0a_top_apply hne]
      exact le_top
    · have he : {ω : ℝ | x < (fun _ => (0:ℝ)) ω} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact hx
      rw [he, measure_empty]
      exact bot_le
  have key := H (⊤ : Measure ℝ) (⊤ : Measure ℝ) _ _ _ hg h 0
  have e1 : {ω : ℝ | (0:ℝ) < ((fun r : ℝ => if 0 ≤ r then (1:ℝ) else 0) ∘
      (fun _ => (0:ℝ))) ω} = Set.univ := by
    ext ω
    simp
  have e2 : {ω : ℝ | (0:ℝ) < ((fun r : ℝ => if 0 ≤ r then (1:ℝ) else 0) ∘
      (fun r => -Real.exp r)) ω} = ∅ := by
    ext ω
    have : ¬ Real.exp ω ≤ 0 := not_le.mpr (Real.exp_pos ω)
    simp [this]
  rw [e1, e2, measure_empty, dp1d0a_top_apply Set.univ_nonempty] at key
  exact absurd key (by simp)

-- Prove2me | solution 1 for ScheduledQueue.Stability.Y_gamma2_finite
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:54:42.942904+00:00
-- url     : https://prove2.me/submissions/043d2b14-53d5-438c-b336-37928da46d8d

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace SQYg2Aux

/-- First Borel–Cantelli lemma for an identically distributed integrable sequence:
almost surely `Z n < n h` for all large `n`. -/
theorem bc_eventually_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : ℝ} (hh : 0 < h) {W : Ω → ℝ} (hW : Integrable W P)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, IdentDistrib (Z n) W P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, Z n ω < n * h := by
  set X : Ω → ℝ := fun ω => max (W ω / h + 1) 0
  have hXint : Integrable X P := ((hW.div_const h).add (integrable_const 1)).pos_part
  have hX0 : 0 ≤ X := fun ω => le_max_right _ _
  have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
  have hle : ∀ n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω} ≤ P {ω | X ω ∈ Ioi (n : ℝ)} := by
    intro n
    have e : P {ω | (n : ℝ) * h ≤ Z n ω} = P {ω | (n : ℝ) * h ≤ W ω} :=
      (hZ n).measure_mem_eq (s := {x | (n : ℝ) * h ≤ x}) (measurableSet_le measurable_const measurable_id)
    rw [e]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, mem_Ioi, X] at hω ⊢
    have : (n : ℝ) ≤ W ω / h := by rw [le_div_iff₀ hh]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsum : (∑' n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω}) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hfin).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa using hn

theorem encard_lt_top_of_eventually {S : Set ℤ} {p : ℕ → Prop}
    (hS : ∀ j ∈ S, 1 ≤ j ∧ p j.toNat) (hev : ∀ᶠ n : ℕ in atTop, ¬ p n) : S.encard < ⊤ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsub : S ⊆ (Finset.Icc (1 : ℤ) N : Set ℤ) := by
    intro j hj
    obtain ⟨h1, h2⟩ := hS j hj
    simp only [Finset.coe_Icc, mem_Icc]
    refine ⟨h1, ?_⟩
    by_contra hc
    exact hN j.toNat (by omega) h2
  exact ((Finset.finite_toSet _).subset hsub).encard_lt_top

end SQYg2Aux

open ScheduledQueue.Stability SQYg2Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, (∀ n : ℕ, Y h ξ n ω < ⊤) ∧ gamma2 h ξ ω < ⊤ := by
  have hY : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
      -ξ ((n : ℤ) + 1 - m) ω + 2 * h < m * h := by
    intro n
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω + 2 * h)
      (hin.integrable.neg.add (integrable_const _))
    intro m
    exact (hin.identDistrib _).comp (u := fun x => -x + 2 * h) (by fun_prop)
  have hG : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, ξ (m : ℤ) ω + h < m * h := by
    apply bc_eventually_lt hh (W := fun ω => ξ 0 ω + h)
      (hin.integrable.add (integrable_const _))
    intro m
    exact (hin.identDistrib _).comp (u := fun x => x + h) (by fun_prop)
  rw [← ae_all_iff] at hY
  filter_upwards [hY, hG] with ω hYω hGω
  refine ⟨fun n => ?_, ?_⟩
  · apply encard_lt_top_of_eventually (p := fun m : ℕ =>
      (((m : ℤ) : ℝ) - 2) * h < -ξ ((n : ℤ) + 1 - (m : ℤ)) ω) _
    · filter_upwards [hYω n] with m hm
      push Not; push_cast; linarith
    · rintro j ⟨hj1, hj2⟩
      refine ⟨hj1, ?_⟩
      show _
      rwa [Int.toNat_of_nonneg (by omega)]
  · apply encard_lt_top_of_eventually (p := fun m : ℕ =>
      (((m : ℤ) : ℝ) - 1) * h ≤ ξ (m : ℤ) ω) _
    · filter_upwards [hGω] with m hm
      push Not; push_cast; linarith
    · rintro j ⟨hj1, hj2⟩
      refine ⟨hj1, ?_⟩
      show _
      rwa [Int.toNat_of_nonneg (by omega)]

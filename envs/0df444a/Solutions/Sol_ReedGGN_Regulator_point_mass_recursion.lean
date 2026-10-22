-- Prove2me | solution 1 for ReedGGN.Regulator.point_mass_recursion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:48:55.099365+00:00
-- url     : https://prove2.me/submissions/15086258-703a-4ccb-b80c-e1f0c09f760d

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

set_option autoImplicit false
open MeasureTheory ReedGGN.Regulator

theorem dirac_int_aux (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ) (t : ℝ) :
    ∫ s in Set.Icc 0 t, f s ∂(Measure.dirac c) = if c ≤ t then f c else 0 := by
  classical
  rw [setIntegral_dirac]
  by_cases h : c ≤ t
  · have : c ∈ Set.Icc 0 t := ⟨hc.le, h⟩
    rw [if_pos this, if_pos h]
  · have : c ∉ Set.Icc 0 t := fun h' => h h'.2
    rw [if_neg this, if_neg h]

theorem solution (c a : ℝ) (hc : 0 < c) :
    (∀ x z : ℝ → ℝ, SolvesRegulator (Measure.dirac c) a x z ↔
      ((∀ t, 0 ≤ t → t < c → z t = x t) ∧
        (∀ t, c ≤ t → z t = x t + max (z (t - c) + a) 0))) ∧
    (∀ x z₁ z₂ : ℝ → ℝ, IsCadlag x → IsCadlag z₁ → IsCadlag z₂ →
      SolvesRegulator (Measure.dirac c) a x z₁ → SolvesRegulator (Measure.dirac c) a x z₂ →
      Set.EqOn z₁ z₂ (Set.Ici 0)) := by
  have key : ∀ x z : ℝ → ℝ, SolvesRegulator (Measure.dirac c) a x z ↔
      ((∀ t, 0 ≤ t → t < c → z t = x t) ∧
        (∀ t, c ≤ t → z t = x t + max (z (t - c) + a) 0)) := by
    intro x z
    unfold SolvesRegulator
    constructor
    · intro h
      refine ⟨fun t ht htc => ?_, fun t htc => ?_⟩
      · rw [h t ht, dirac_int_aux c hc, if_neg (not_le.mpr htc), add_zero]
      · rw [h t (hc.le.trans htc), dirac_int_aux c hc, if_pos htc]
    · rintro ⟨h1, h2⟩ t ht
      rw [dirac_int_aux c hc]
      by_cases htc : c ≤ t
      · rw [if_pos htc, h2 t htc]
      · rw [if_neg htc, add_zero]
        exact h1 t ht (not_le.mp htc)
  refine ⟨key, ?_⟩
  intro x z₁ z₂ _ _ _ hs₁ hs₂
  rw [key] at hs₁ hs₂
  have main : ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → t < k * c → z₁ t = z₂ t := by
    intro k
    induction k with
    | zero => intro t ht htk; simp at htk; linarith
    | succ k ih =>
      intro t ht htk
      by_cases htc : t < c
      · rw [hs₁.1 t ht htc, hs₂.1 t ht htc]
      · have htc' : c ≤ t := not_lt.mp htc
        rw [hs₁.2 t htc', hs₂.2 t htc', ih (t - c) (by linarith) (by push_cast at htk; linarith)]
  intro t ht
  obtain ⟨k, hk⟩ := exists_nat_gt (t / c)
  have : t < k * c := by
    have := (div_lt_iff₀ hc).mp hk
    linarith
  exact main k t ht this

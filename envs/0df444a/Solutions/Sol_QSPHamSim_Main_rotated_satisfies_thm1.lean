-- Prove2me | solution 1 for QSPHamSim.Main.rotated_satisfies_thm1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:45:01.120984+00:00
-- url     : https://prove2.me/submissions/6295dec0-9b10-4a55-9341-4f4b8bfbcc0b

import Definitions.Def_QSPHamSim_Main_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open QSPHamSim.Main

theorem solution (M : ℕ) (A₁ B C₁ D : ℝ → ℝ)
    (hA : IsCosSeries M A₁) (hB : IsCosSeries M B)
    (hC : IsSinSeries M C₁) (hD : IsSinSeries M D)
    (hunit : ∀ θ : ℝ,
      A₁ θ ^ 2 + B θ ^ 2 + C₁ θ ^ 2 + D θ ^ 2 = 1)
    (δ : ℝ) (hcos : Real.cos δ = A₁ 0)
    (hsin : Real.sin δ = B 0) :
    let A₂ := fun θ : ℝ => A₁ θ * Real.cos δ + B θ * Real.sin δ
    A₂ 0 = 1 ∧ IsCosSeries M A₂ ∧
      (∀ θ : ℝ, A₂ θ ^ 2 + C₁ θ ^ 2 ≤ 1) := by
  dsimp only
  have hC0 : C₁ 0 = 0 := by
    obtain ⟨c, hc⟩ := hC
    simpa using hc 0
  have hD0 : D 0 = 0 := by
    obtain ⟨d, hd⟩ := hD
    simpa using hd 0
  refine ⟨?_, ?_, ?_⟩
  · have ht := hunit 0
    rw [hC0, hD0] at ht
    rw [hcos, hsin]
    nlinarith only [ht]
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨fun k => a k * Real.cos δ + b k * Real.sin δ, ?_⟩
    intro θ
    dsimp only
    rw [ha θ, hb θ]
    simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring
  · intro θ
    have hid : (A₁ θ * Real.cos δ + B θ * Real.sin δ) ^ 2 +
        (A₁ θ * Real.sin δ - B θ * Real.cos δ) ^ 2 =
        (A₁ θ ^ 2 + B θ ^ 2) * (Real.sin δ ^ 2 + Real.cos δ ^ 2) := by ring
    rw [Real.sin_sq_add_cos_sq, mul_one] at hid
    linarith only [hid, hunit θ, sq_nonneg (A₁ θ * Real.sin δ - B θ * Real.cos δ), sq_nonneg (D θ)]

#print axioms solution

-- Prove2me | solution 1 for WeakMFG.Uniqueness.eq_7_11_7_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:30:54.194478+00:00
-- url     : https://prove2.me/submissions/1a370e3b-76dd-43a2-ba85-2a9eb2d8ed5d

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_AssumptionU

open WeakMFG.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

theorem solution {d : ℕ} {T : ℝ≥0}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (ψ : WeakMFG.Existence.Path d T → ℝ) (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (hS1 : S1 A σ b) (hS3 : S3 A f g)
    (b₀ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → (Fin d → ℝ)) (hb₀ : ∀ t x μ a, b t x μ a = b₀ t x a)
    (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) (f₂ : ℝ≥0 → Ppsi ψ → PA A → ℝ)
    (f₃ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → ℝ) (hdec : IsU3Decomp f f₁ f₂ f₃)
    (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (z : Fin d → ℝ) (μ₁ μ₂ : Ppsi ψ) (q₁ q₂ : PA A) (a₁ a₂ : EA)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ Amax A σ b f t x μ₂ q₂ z) :
    (f t x μ₁ q₁ a₁ - f t x μ₂ q₂ a₂ + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b₀ t x a₁ - (σ t x)⁻¹ *ᵥ b₀ t x a₂) ≤
        f₁ t x μ₁ - f₁ t x μ₂ + f₂ t μ₁ q₁ - f₂ t μ₂ q₂) ∧
    (U1 A σ b f → a₁ ≠ a₂ →
      f t x μ₁ q₁ a₁ - f t x μ₂ q₂ a₂ + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b₀ t x a₁ - (σ t x)⁻¹ *ᵥ b₀ t x a₂) <
        f₁ t x μ₁ - f₁ t x μ₂ + f₂ t μ₁ q₁ - f₂ t μ₂ q₂) := by
  obtain ⟨H, hHdef⟩ : ∃ H, H = ham σ b f t x μ₂ q₂ z := ⟨_, rfl⟩
  have hmax : H a₂ = sSup (H '' A) := by rw [hHdef]; exact ha₂.2
  have hH : ∀ a, H a = f₁ t x μ₂ + f₂ t μ₂ q₂ + f₃ t x a + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b₀ t x a) := by
    intro a
    simp only [hHdef, ham, hdec t x μ₂ q₂ a, hb₀]
  have key : f t x μ₁ q₁ a₁ - f t x μ₂ q₂ a₂ + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b₀ t x a₁ - (σ t x)⁻¹ *ᵥ b₀ t x a₂)
      = (f₁ t x μ₁ - f₁ t x μ₂ + f₂ t μ₁ q₁ - f₂ t μ₂ q₂) + (H a₁ - H a₂) := by
    rw [hH, hH, hdec t x μ₁ q₁ a₁, hdec t x μ₂ q₂ a₂, dotProduct_sub]
    ring
  have hcont : ContinuousOn H A := by
    rw [hHdef]
    have h1 := hS3.2.1 t x μ₂ q₂
    have h2 := hS1.2.2.2.2 t x μ₂
    have hlin : Continuous (fun v : Fin d → ℝ => z ⬝ᵥ ((σ t x)⁻¹ *ᵥ v)) := by fun_prop
    exact h1.add (hlin.comp_continuousOn h2)
  have hbdd : BddAbove (H '' A) := (hS1.1.image_of_continuousOn hcont).bddAbove
  have hle : H a₁ ≤ H a₂ := by
    rw [hmax]
    exact le_csSup hbdd ⟨a₁, ha₁, rfl⟩
  refine ⟨by rw [key]; linarith, fun hU hne => ?_⟩
  obtain ⟨a, ha⟩ := hU t x μ₂ q₂ z
  have hlt : H a₁ < H a₂ := by
    refine lt_of_le_of_ne hle (fun heq => hne ?_)
    have h1 : a₁ ∈ Amax A σ b f t x μ₂ q₂ z := ⟨ha₁, by
      have := heq.trans hmax; rw [hHdef] at this; exact this⟩
    rw [ha] at h1 ha₂
    exact h1.trans ha₂.symm
  rw [key]; linarith

-- Prove2me | solution 1 for OTDRO.StrongCvx.dual_optimizer_in_V
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:49:41.444237+00:00
-- url     : https://prove2.me/submissions/be7eadb0-5f5d-49cb-ab19-420a25324ae5

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Regions
import Theorems.Thm_OTDRO_StrongCvx_dual_optimizer_bounds

open MeasureTheory

theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ) (hL : OTDRO.StrongCvx.DerivSqBounds P0 ℓ B Llow Lbar)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B)
    (lamStar : ℝ) (hlam : 0 ≤ lamStar)
    (hmin : IsMinOn (fun lam => OTDRO.Dual.fDelta P0 ℓ A δ β lam) (Set.Ici 0) lamStar) :
    (β, lamStar) ∈ OTDRO.StrongCvx.regionV B δ M (OTDRO.StrongCvx.Rbeta B) ρmin ρmax Llow Lbar := by
  obtain ⟨hlow, hup⟩ := OTDRO.StrongCvx.dual_optimizer_bounds P0 A ρmin ρmax hA ℓ h2 δ hδ B hB M
    h3 β hβB lamStar hlam hmin
  obtain ⟨hLl, hLb, hLβ⟩ := hL
  obtain ⟨-, hEl, hEu⟩ := hLβ β hβB
  set E := ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0
  have hρ := hA.rhoMin_pos
  have hρM := hA.rhoMax_pos
  have hM := h3.M_pos
  have hbdd : BddAbove ((fun β : EuclideanSpace ℝ (Fin d) => ‖β‖) '' B) :=
    (hB4.compact.image continuous_norm).isBounded.bddAbove
  have hnormR : ‖β‖ ≤ OTDRO.StrongCvx.Rbeta B := le_csSup hbdd ⟨β, hβB, rfl⟩
  refine ⟨hβB, hlam, ?_, ?_⟩
  · -- K1 ‖β‖ ≤ λ*
    unfold OTDRO.StrongCvx.K1
    have h1 : Real.sqrt (Llow / ρmax) ≤ Real.sqrt E / Real.sqrt ρmax := by
      rw [← Real.sqrt_div' _ hρM.le]
      exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hEl hρM.le)
    have h2' : 1 / 2 * Real.sqrt (Llow / ρmax) * ‖β‖ ≤
        1 / 2 / Real.sqrt ρmax * ‖β‖ * Real.sqrt E := by
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg β)
      have e : 1 / 2 / Real.sqrt ρmax * ‖β‖ * Real.sqrt E =
          1 / 2 * (Real.sqrt E / Real.sqrt ρmax * ‖β‖) := by ring
      rw [e]; nlinarith
    exact h2'.trans hlow
  · -- λ* ≤ K2 ‖β‖
    unfold OTDRO.StrongCvx.K2
    have h1 : Real.sqrt E / Real.sqrt ρmin ≤ Real.sqrt (Lbar / ρmin) := by
      rw [← Real.sqrt_div' _ hρ.le]
      exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hEu hρ.le)
    have h2' : 1 / Real.sqrt ρmin * ‖β‖ * Real.sqrt E ≤ Real.sqrt (Lbar / ρmin) * ‖β‖ := by
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg β)
      have e : 1 / Real.sqrt ρmin * ‖β‖ * Real.sqrt E = Real.sqrt E / Real.sqrt ρmin * ‖β‖ := by
        ring
      rw [e]; exact this
    have h3' : 1 / 2 * Real.sqrt δ * M / ρmin * ‖β‖ ^ 2 ≤
        1 / 2 * Real.sqrt δ * M * OTDRO.StrongCvx.Rbeta B / ρmin * ‖β‖ := by
      have hc : 0 ≤ 1 / 2 * Real.sqrt δ * M / ρmin := by positivity
      have := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hnormR (norm_nonneg β)) hc
      have e1 : 1 / 2 * Real.sqrt δ * M / ρmin * ‖β‖ ^ 2 =
          1 / 2 * Real.sqrt δ * M / ρmin * (‖β‖ * ‖β‖) := by ring
      have e2 : 1 / 2 * Real.sqrt δ * M * OTDRO.StrongCvx.Rbeta B / ρmin * ‖β‖ =
          1 / 2 * Real.sqrt δ * M / ρmin * (OTDRO.StrongCvx.Rbeta B * ‖β‖) := by ring
      rw [e1, e2]; exact this
    show lamStar ≤ (1 / 2 * Real.sqrt δ * M * OTDRO.StrongCvx.Rbeta B / ρmin +
      Real.sqrt (Lbar / ρmin)) * ‖β‖
    nlinarith

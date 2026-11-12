-- Prove2me | solution 1 for SurrogateOps.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:14:51.698074+00:00
-- url     : https://prove2.me/submissions/6c57634b-d233-4c52-8d1c-1426a6b94b98

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt

open SurrogateOps in
theorem solution {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar N₁ N₂ κ₁ κ₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 1 f₁) (hf₂ : ContDiff ℝ 1 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₁ Δ) x0)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₂ Δ) x0)
    (he₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₁ Δ x0 = f₁ x0)
    (he₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₂ Δ x0 = f₂ x0)
    (hg₁ : GradAccAt f₁ fm₁ x0 Δbar N₁ κ₁)
    (hg₂ : GradAccAt f₂ fm₂ x0 Δbar N₂ κ₂)
    (hNF : NF = min N₁ N₂)
    (hK : K = |f₂ x0| * κ₁ * Δbar ^ (N₁ - NF) + |f₁ x0| * κ₂ * Δbar ^ (N₂ - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fun x => f₁ x * f₂ x) x0 - fderiv ℝ (fun x => fm₁ Δ x * fm₂ Δ x) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, GradAccAt (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ := by
  obtain ⟨hN1, hk1, hb1⟩ := hg₁
  obtain ⟨hN2, hk2, hb2⟩ := hg₂
  have hNF1 : NF ≤ N₁ := by rw [hNF]; exact min_le_left _ _
  have hNF2 : NF ≤ N₂ := by rw [hNF]; exact min_le_right _ _
  have hNF0 : 0 ≤ NF := by rw [hNF]; exact le_min hN1 hN2
  have hd1 : DifferentiableAt ℝ f₁ x0 := (hf₁.differentiable one_ne_zero) x0
  have hd2 : DifferentiableAt ℝ f₂ x0 := (hf₂.differentiable one_ne_zero) x0
  have hK0 : 0 ≤ K := by
    rw [hK]
    have a1 : 0 ≤ Δbar ^ (N₁ - NF) := Real.rpow_nonneg hΔbar.le _
    have a2 : 0 ≤ Δbar ^ (N₂ - NF) := Real.rpow_nonneg hΔbar.le _
    exact add_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hk1) a1)
      (mul_nonneg (mul_nonneg (abs_nonneg _) hk2) a2)
  have main : ∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fun x => f₁ x * f₂ x) x0 - fderiv ℝ (fun x => fm₁ Δ x * fm₂ Δ x) x0‖
        ≤ K * Δ ^ NF := by
    intro Δ hΔ
    obtain ⟨hΔ0, hΔ1⟩ := hΔ
    have pw : ∀ N : ℝ, NF ≤ N → Δ ^ N ≤ Δbar ^ (N - NF) * Δ ^ NF := by
      intro N hN
      have e : Δ ^ N = Δ ^ (N - NF) * Δ ^ NF := by
        rw [← Real.rpow_add hΔ0, sub_add_cancel]
      rw [e]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hΔ0.le hΔ1 (by linarith))
        (Real.rpow_nonneg hΔ0.le _)
    have p1 := pw N₁ hNF1
    have p2 := pw N₂ hNF2
    have b1 := hb1 Δ ⟨hΔ0, hΔ1⟩
    have b2 := hb2 Δ ⟨hΔ0, hΔ1⟩
    rw [fderiv_fun_mul hd1 hd2, fderiv_fun_mul (hm₁ Δ ⟨hΔ0, hΔ1⟩) (hm₂ Δ ⟨hΔ0, hΔ1⟩),
      he₁ Δ ⟨hΔ0, hΔ1⟩, he₂ Δ ⟨hΔ0, hΔ1⟩]
    have heq : f₁ x0 • fderiv ℝ f₂ x0 + f₂ x0 • fderiv ℝ f₁ x0 -
        (f₁ x0 • fderiv ℝ (fm₂ Δ) x0 + f₂ x0 • fderiv ℝ (fm₁ Δ) x0) =
        f₁ x0 • (fderiv ℝ f₂ x0 - fderiv ℝ (fm₂ Δ) x0) +
          f₂ x0 • (fderiv ℝ f₁ x0 - fderiv ℝ (fm₁ Δ) x0) := by
      rw [smul_sub, smul_sub]
      abel
    rw [heq]
    have t1 := norm_add_le (f₁ x0 • (fderiv ℝ f₂ x0 - fderiv ℝ (fm₂ Δ) x0))
      (f₂ x0 • (fderiv ℝ f₁ x0 - fderiv ℝ (fm₁ Δ) x0))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at t1
    have c1 : |f₁ x0| * ‖fderiv ℝ f₂ x0 - fderiv ℝ (fm₂ Δ) x0‖ ≤ |f₁ x0| * (κ₂ * Δ ^ N₂) :=
      mul_le_mul_of_nonneg_left b2 (abs_nonneg _)
    have c2 : |f₂ x0| * ‖fderiv ℝ f₁ x0 - fderiv ℝ (fm₁ Δ) x0‖ ≤ |f₂ x0| * (κ₁ * Δ ^ N₁) :=
      mul_le_mul_of_nonneg_left b1 (abs_nonneg _)
    have c3 : |f₁ x0| * κ₂ * Δ ^ N₂ ≤ |f₁ x0| * κ₂ * (Δbar ^ (N₂ - NF) * Δ ^ NF) :=
      mul_le_mul_of_nonneg_left p2 (mul_nonneg (abs_nonneg _) hk2)
    have c4 : |f₂ x0| * κ₁ * Δ ^ N₁ ≤ |f₂ x0| * κ₁ * (Δbar ^ (N₁ - NF) * Δ ^ NF) :=
      mul_le_mul_of_nonneg_left p1 (mul_nonneg (abs_nonneg _) hk1)
    rw [hK]
    nlinarith
  exact ⟨main, K, hNF0, hK0, main⟩

-- Prove2me | solution 1 for RelSmoothFOM.DOptimal.eq_41_42
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:36:23.006955+00:00
-- url     : https://prove2.me/submissions/8ee9d933-8e22-4d72-8754-6a43b87027ca

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

set_option autoImplicit false
open RelSmoothFOM.DOptimal

/-- derivative of the log barrier at a positive point -/
theorem rsd_logBarrier_fderiv {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) (v : Fin n → ℝ) :
    fderiv ℝ (logBarrier : (Fin n → ℝ) → ℝ) x v = -∑ j, v j / x j := by
  have h : HasFDerivAt (logBarrier : (Fin n → ℝ) → ℝ)
      (-∑ j : Fin n, (x j)⁻¹ • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        HasFDerivAt (fun y : Fin n → ℝ => Real.log (y j))
          ((x j)⁻¹ • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
      intro j _
      exact (hasFDerivAt_apply j x).log (hx j).ne'
    have := (HasFDerivAt.sum h1).neg
    have hf : (logBarrier : (Fin n → ℝ) → ℝ) = -∑ i : Fin n, fun y : Fin n → ℝ => Real.log (y i) := by
      funext y
      simp [logBarrier]
    rw [hf]
    exact this
  rw [h.fderiv]
  simp [div_eq_inv_mul]

theorem solution {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (xhat : Fin n → ℝ) (hh : xhat ∈ posSimplex n)
    (hlower : ∀ j, δ / (n : ℝ) ≤ xhat j) :
    let x0 : Fin n → ℝ := fun _ => 1 / (n : ℝ)
    RelSmoothFOM.PrimalGrad.bregman logBarrier xhat x0 = logBarrier xhat - logBarrier x0 ∧
      logBarrier xhat - logBarrier x0 ≤ (n : ℝ) * Real.log (1 / δ) := by
  intro x0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : ∀ j, 0 < x0 j := fun j => by simp only [x0]; positivity
  constructor
  · unfold RelSmoothFOM.PrimalGrad.bregman
    rw [rsd_logBarrier_fderiv x0 hx0]
    have : ∑ j, (xhat - x0) j / x0 j = 0 := by
      have e : ∀ j, (xhat - x0) j / x0 j = (n : ℝ) * xhat j - 1 := by
        intro j
        simp only [Pi.sub_apply, x0]
        field_simp
      simp only [e]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hh.2]
      simp
    rw [this]; ring
  · have h1 : ∑ j, Real.log (δ / n) ≤ ∑ j, Real.log (xhat j) :=
      Finset.sum_le_sum fun j _ => Real.log_le_log (by positivity) (hlower j)
    have h2 : logBarrier xhat - logBarrier x0 = -∑ j, Real.log (xhat j) + ∑ j : Fin n, Real.log (1 / (n:ℝ)) := by
      simp [logBarrier, x0]
      ring
    rw [h2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 ⊢
    have e1 : Real.log (δ / n) = Real.log δ - Real.log n := Real.log_div hδ.ne' hnpos.ne'
    have e2 : Real.log (1 / (n:ℝ)) = - Real.log n := by simp
    have e3 : Real.log (1 / δ) = - Real.log δ := by simp
    rw [e1] at h1
    rw [e2, e3]
    nlinarith

-- Prove2me | solution 2 for WeilConjectures.exists_unit_equiv_of_snf_diag_eq
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T13:27:32.366826+00:00
-- url     : https://prove2.me/submissions/df68457f-37b7-4961-b71f-d1f6b20fb52d

import Mathlib

/-!
A41a / 0-child: equal SNF diagonals ⇒ unit equivalence by composing Smith factorizations.
From `P₁ M Q₁ = diag(d M) = diag(d N) = P₂ N Q₂` get
`N = (P₂⁻¹ P₁) M (Q₁ Q₂⁻¹)` with unit dets via `Matrix.isUnit_nonsing_inv_det`.
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hfac : ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * M * Q = Matrix.diagonal (d M))
    {M N : Matrix ι ι (Polynomial K)}
    (h : d M = d N) :
    ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * M * Q = N := by
  classical
  obtain ⟨PM, QM, hPM, hQM, hM⟩ := hfac M
  obtain ⟨PN, QN, hPN, hQN, hN⟩ := hfac N
  rw [h, ← hN] at hM
  have iPN : PN⁻¹ * PN = 1 := Matrix.nonsing_inv_mul _ hPN
  have iQN : QN * QN⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQN
  refine ⟨PN⁻¹ * PM, QM * QN⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ hPN).mul hPM
  · rw [Matrix.det_mul]
    exact hQM.mul (Matrix.isUnit_nonsing_inv_det _ hQN)
  · calc PN⁻¹ * PM * M * (QM * QN⁻¹) = PN⁻¹ * (PM * M * QM) * QN⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = PN⁻¹ * (PN * N * QN) * QN⁻¹ := by rw [hM]
      _ = N := by
          simp only [← Matrix.mul_assoc, iPN, Matrix.one_mul]
          rw [Matrix.mul_assoc, iQN, Matrix.mul_one]

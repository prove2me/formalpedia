-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.jamiolkowski_isDensity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:42:07.472328+00:00
-- url     : https://prove2.me/submissions/b0a42d15-6395-47ac-86ad-d9febac6f536

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct
open QAlgorithms.Papers.Independent.Frontier18.P17
open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)
open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

theorem solution {N : ℕ} (hN : 0 < N)
    (Phi : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (hPhi : CPTP Phi) :
    (dynamical Phi).PosSemidef ∧ (dynamical Phi).trace = (N : ℂ) ∧
      QAlgorithms.IsDensityMatrix (jamiolkowski Phi) := by
  obtain ⟨hCP, hTP⟩ := hPhi
  let Ω : Fin N × Fin N → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hX := Matrix.posSemidef_vecMulVec_self_star Ω
  have hY := hCP N _ hX
  have hE : ∀ a a' : Fin N, (Matrix.of fun i i' => Matrix.vecMulVec Ω (star Ω) (a, i) (a', i')) =
      Matrix.single a a' 1 := by
    intro a a'
    ext i i'
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, Ω, Matrix.single_apply]
    by_cases h1 : a = i <;> by_cases h2 : a' = i' <;> simp [h1, h2]
  have hdyn : dynamical Phi = (QAlgorithms.idTensorSuperop Phi (Matrix.vecMulVec Ω (star Ω))).submatrix
      (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext p q
    simp only [dynamical, Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, QAlgorithms.idTensorSuperop, Matrix.of_apply]
    rw [hE]
  have hpsd : (dynamical Phi).PosSemidef := by
    rw [hdyn]; exact hY.submatrix _
  have htr : (dynamical Phi).trace = (N : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, dynamical, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have : ∀ a : Fin N, ∑ j, Phi (Matrix.single a a 1) j j = 1 := by
      intro a
      have := hTP (Matrix.single a a 1)
      simp only [Matrix.trace, Matrix.diag] at this
      rw [this]; simp [Matrix.single_apply]
    simp [this]
  refine ⟨hpsd, htr, ?_, ?_⟩
  · unfold jamiolkowski
    have hc : (0 : ℂ) ≤ ((Fintype.card (Fin N) : ℂ))⁻¹ := by
      rw [Fintype.card_fin]
      exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le N)
    exact hpsd.smul hc
  · unfold jamiolkowski
    rw [Matrix.trace_smul, htr, Fintype.card_fin, smul_eq_mul]
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp

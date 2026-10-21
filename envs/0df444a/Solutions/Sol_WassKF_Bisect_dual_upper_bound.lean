-- Prove2me | solution 1 for WassKF.Bisect.dual_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:18:07.755486+00:00
-- url     : https://prove2.me/submissions/d95c213f-df06-4207-8509-2a4b1c9fa0a6

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet

set_option autoImplicit false

open Matrix

section psd
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma psd_exists_sqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) : ∃ S : Matrix n n ℝ, S.PosSemidef ∧ S * S = A := by
  have h0 : (0 : Matrix n n ℝ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  exact ⟨CFC.sqrt A, Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A),
    CFC.sqrt_mul_sqrt_self A h0⟩

lemma psd_unique {n : Type*} [Fintype n] [DecidableEq n] (B B' : Matrix n n ℝ)
    (hB : B.PosSemidef) (hB' : B'.PosSemidef) (h : B' * B' = B * B) : B' = B := by
  have hB0 : (0 : Matrix n n ℝ) ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
  have hB0' : (0 : Matrix n n ℝ) ≤ B' := Matrix.nonneg_iff_posSemidef.mpr hB'
  exact (CFC.mul_self_eq_mul_self_iff B' B hB0' hB0).mp h

lemma psd_commute_mul {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℝ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : X * Y = Y * X) : (X * Y).PosSemidef := by
  have hX0 : (0 : Matrix n n ℝ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
  have hY0 : (0 : Matrix n n ℝ) ≤ Y := Matrix.nonneg_iff_posSemidef.mpr hY
  exact Matrix.nonneg_iff_posSemidef.mp (Commute.mul_nonneg hX0 hY0 h)

end psd

lemma psdSqrt_unique {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hB : B.PosSemidef) (hBB : B * B = A) :
    WassersteinDRO.Shrinkage.psdSqrt A = B := by
  classical
  unfold WassersteinDRO.Shrinkage.psdSqrt
  have hex : ∃ B' : Matrix n n ℝ, B'.PosSemidef ∧ B' * B' = A := ⟨B, hB, hBB⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact psd_unique B _ hB h1 (by rw [h2, hBB])


lemma psdSqrt_spec {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ)
    (hW : W.PosSemidef) :
    (WassersteinDRO.Shrinkage.psdSqrt W).PosSemidef ∧
      WassersteinDRO.Shrinkage.psdSqrt W * WassersteinDRO.Shrinkage.psdSqrt W = W := by
  classical
  obtain ⟨B, hB, hBB⟩ := psd_exists_sqrt W hW
  have : WassersteinDRO.Shrinkage.psdSqrt W = B := psdSqrt_unique W B hB hBB
  rw [this]; exact ⟨hB, hBB⟩

theorem solution {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (L' : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (hL' : L' ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ) :
    (L'ᵀ * D).trace ≤
      γ * (ρ ^ 2 - Sigma.trace) +
        γ ^ 2 * (((γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)⁻¹)ᵀ * Sigma).trace := by
  classical
  obtain ⟨hX, -, -, htr, -⟩ := hL'
  have hSigT : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hDT : Dᵀ = D := by simpa using hD.isHermitian.eq
  have hXT : L'ᵀ = L' := by simpa using hX.isHermitian.eq
  rcases isEmpty_or_nonempty (Fin n ⊕ Fin m) with hE | hNE
  · have hz : ∀ M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ, M.trace = 0 := fun M => by
      simp [Matrix.trace, Finset.univ_eq_empty]
    simp only [hz, mul_zero, sub_zero, add_zero]
    exact mul_nonneg hγ0 (sq_nonneg ρ)
  obtain ⟨A, hAdef⟩ : ∃ A, A = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D := ⟨_, rfl⟩
  rw [← hAdef] at hγ ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = A⁻¹ := ⟨_, rfl⟩
  rw [← ha]
  have hγpos : 0 < γ := by
    obtain ⟨i⟩ := hNE
    have h1 := hγ.diag_pos (i := i)
    have h2 := hD.diag_nonneg (i := i)
    rw [hAdef] at h1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    linarith
  have hAT : Aᵀ = A := by rw [hAdef]; simp [hDT]
  have hAu : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hγ.isUnit
  have hAa : A * a = 1 := by rw [ha]; exact Matrix.mul_nonsing_inv _ hAu
  have haA : a * A = 1 := by rw [ha]; exact Matrix.nonsing_inv_mul _ hAu
  have haT : aᵀ = a := by rw [ha, Matrix.transpose_nonsing_inv, hAT]
  have hDA : D = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - A := by
    rw [hAdef, sub_sub_cancel]
  -- square root of Sigma
  obtain ⟨R, hR, hRR⟩ := psd_exists_sqrt Sigma hSigma.posSemidef
  have hRT : Rᵀ = R := by simpa using hR.isHermitian.eq
  have hpsdR : WassersteinDRO.Shrinkage.psdSqrt Sigma = R := psdSqrt_unique _ _ hR hRR
  have hRu : IsUnit R.det := by
    have h1 : IsUnit (R * R).det := by
      rw [hRR]; exact (isUnit_iff_isUnit_det _).mp hSigma.isUnit
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨Ri, hRi⟩ : ∃ Ri, Ri = R⁻¹ := ⟨_, rfl⟩
  have hRRi : R * Ri = 1 := by rw [hRi]; exact Matrix.mul_nonsing_inv _ hRu
  have hRiR : Ri * R = 1 := by rw [hRi]; exact Matrix.nonsing_inv_mul _ hRu
  have hRiT : Riᵀ = Ri := by rw [hRi, Matrix.transpose_nonsing_inv, hRT]
  -- Y
  have hWpsd : (R * L' * R).PosSemidef := by
    have := hX.conjTranspose_mul_mul_same R
    have h2 : Rᴴ = R := by simpa using hRT
    rw [h2] at this
    exact this
  obtain ⟨hYpsd, hYY⟩ := psdSqrt_spec _ hWpsd
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = WassersteinDRO.Shrinkage.psdSqrt (R * L' * R) := ⟨_, rfl⟩
  rw [← hYdef] at hYpsd hYY
  rw [hpsdR, ← hYdef] at htr
  have hYT : Yᵀ = Y := by simpa using hYpsd.isHermitian.eq
  -- P and Q
  obtain ⟨P, hPdef⟩ : ∃ P, P = γ • (R * a * R) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = γ⁻¹ • (Ri * A * Ri) := ⟨_, rfl⟩
  have hγne : γ ≠ 0 := hγpos.ne'
  have hPQ : P * Q = 1 := by
    rw [hPdef, hQdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hγne, one_smul]
    calc R * a * R * (Ri * A * Ri) = R * a * (R * Ri) * A * Ri := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hRRi, Matrix.mul_one]
        calc R * a * A * Ri = R * (a * A) * Ri := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [haA, Matrix.mul_one, hRRi]
  have hQP : Q * P = 1 := by
    rw [hPdef, hQdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hγne, one_smul]
    calc Ri * A * Ri * (R * a * R) = Ri * A * (Ri * R) * a * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hRiR, Matrix.mul_one]
        calc Ri * A * a * R = Ri * (A * a) * R := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hAa, Matrix.mul_one, hRiR]
  have hQpsd : Q.PosSemidef := by
    have := hγ.posSemidef.conjTranspose_mul_mul_same Ri
    have h2 : Riᴴ = Ri := by simpa using hRiT
    rw [h2] at this
    rw [hQdef]
    exact this.smul (inv_nonneg.mpr hγ0)
  have hPT : Pᵀ = P := by
    rw [hPdef, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, hRT, haT,
      Matrix.mul_assoc]
  have hkey : 0 ≤ ((P - Y) * Q * (P - Y)).trace := by
    have := hQpsd.conjTranspose_mul_mul_same (P - Y)
    have h2 : (P - Y)ᴴ = P - Y := by simp [Matrix.conjTranspose_eq_transpose_of_trivial, hPT, hYT]
    rw [h2] at this
    exact this.trace_nonneg
  have hexp : (P - Y) * Q * (P - Y) = P - Y - Y + Y * Q * Y := by
    have e1 : P * Q * P = P := by rw [hPQ, Matrix.one_mul]
    have e2 : P * Q * Y = Y := by rw [hPQ, Matrix.one_mul]
    have e3 : Y * Q * P = Y := by rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, e1, e2, e3]
    abel
  have htrP : P.trace = γ * (a * Sigma).trace := by
    rw [hPdef, Matrix.trace_smul, smul_eq_mul]
    congr 1
    calc (R * a * R).trace = (R * (a * R)).trace := by rw [Matrix.mul_assoc]
      _ = ((a * R) * R).trace := Matrix.trace_mul_comm _ _
      _ = (a * Sigma).trace := by rw [Matrix.mul_assoc, hRR]
  have htrYQY : (Y * Q * Y).trace = γ⁻¹ * (A * L').trace := by
    calc (Y * Q * Y).trace = (Q * (Y * Y)).trace := by
          calc (Y * Q * Y).trace = (Y * (Q * Y)).trace := by rw [Matrix.mul_assoc]
            _ = ((Q * Y) * Y).trace := Matrix.trace_mul_comm _ _
            _ = (Q * (Y * Y)).trace := by rw [Matrix.mul_assoc]
      _ = (Q * (R * L' * R)).trace := by rw [hYY]
      _ = γ⁻¹ * (A * L').trace := by
          rw [hQdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
          congr 1
          calc (Ri * A * Ri * (R * L' * R)).trace = (Ri * (A * L') * R).trace := by
                rw [show Ri * A * Ri * (R * L' * R) = Ri * A * (Ri * R) * L' * R by
                  simp only [Matrix.mul_assoc], hRiR, Matrix.mul_one]
                simp only [Matrix.mul_assoc]
            _ = (Ri * ((A * L') * R)).trace := by rw [Matrix.mul_assoc]
            _ = (((A * L') * R) * Ri).trace := Matrix.trace_mul_comm _ _
            _ = (A * L').trace := by rw [Matrix.mul_assoc, hRRi, Matrix.mul_one]
  rw [hexp] at hkey
  simp only [Matrix.trace_add, Matrix.trace_sub, htrP, htrYQY] at hkey
  -- the inequality 2γ tr Y ≤ γ² tr(aΣ) + tr(A L')
  have h2 : 2 * γ * Y.trace ≤ γ ^ 2 * (a * Sigma).trace + (A * L').trace := by
    have := mul_nonneg hγpos.le hkey
    have e : γ * (γ * (a * Sigma).trace - Y.trace - Y.trace + γ⁻¹ * (A * L').trace) =
        γ ^ 2 * (a * Sigma).trace - 2 * γ * Y.trace + (A * L').trace := by
      field_simp
      ring
    linarith
  -- trace condition
  have htr' : L'.trace + Sigma.trace - 2 * Y.trace ≤ ρ ^ 2 := by
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at htr
    linarith
  have hZ : (aᵀ * Sigma).trace = (a * Sigma).trace := by rw [haT]
  have hLD : (L'ᵀ * D).trace = γ * L'.trace - (A * L').trace := by
    rw [hXT, hDA, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, Matrix.trace_mul_comm]
  rw [hZ, hLD]
  nlinarith [mul_le_mul_of_nonneg_left htr' hγ0, h2]

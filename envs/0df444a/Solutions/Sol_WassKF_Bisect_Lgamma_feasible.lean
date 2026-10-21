-- Prove2me | solution 1 for WassKF.Bisect.Lgamma_feasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:18:06.464281+00:00
-- url     : https://prove2.me/submissions/f9f7d9c1-e37a-4376-84e7-7d98bb4cdfea

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
import Definitions.Def_WassKF_Bisect_hFun
import Definitions.Def_WassKF_Bisect_Lgamma

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

open WassKF.Bisect

theorem solution {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ σ γ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (hh : 0 < hFun Sigma D ρ γ) :
    Lgamma Sigma D γ ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ := by
  classical
  unfold hFun at hh
  unfold Lgamma
  have hSigT : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hDT : Dᵀ = D := by simpa using hD.isHermitian.eq
  obtain ⟨A, hAdef⟩ : ∃ A, A = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D := ⟨_, rfl⟩
  rw [← hAdef] at hγ hh ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = A⁻¹ := ⟨_, rfl⟩
  rw [← ha] at hh ⊢
  have hAT : Aᵀ = A := by rw [hAdef]; simp [hDT]
  have hAu : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hγ.isUnit
  have hAa : A * a = 1 := by rw [ha]; exact Matrix.mul_nonsing_inv _ hAu
  have haA : a * A = 1 := by rw [ha]; exact Matrix.nonsing_inv_mul _ hAu
  have haT : aᵀ = a := by rw [ha, Matrix.transpose_nonsing_inv, hAT]
  have hapd : a.PosDef := by rw [ha]; exact hγ.inv
  have hDA : D = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - A := by
    rw [hAdef, sub_sub_cancel]
  -- σ ≥ 0
  have hσpos : 0 ≤ σ := by
    obtain ⟨v, hv, hvσ⟩ := hσ_eig
    have h1 := hSigma.dotProduct_mulVec_pos hv
    rw [hvσ] at h1
    simp only [star_trivial, dotProduct_smul, smul_eq_mul] at h1
    have h2 : 0 < v ⬝ᵥ v := by
      by_contra hneg
      have : v ⬝ᵥ v = 0 := le_antisymm (not_lt.mp hneg) (dotProduct_self_star_nonneg v)
      exact hv ((dotProduct_self_eq_zero).mp this)
    by_contra hneg
    have : σ * (v ⬝ᵥ v) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) h2
    linarith
  -- empty case / γ ≥ 0
  rcases isEmpty_or_nonempty (Fin n ⊕ Fin m) with hE | hNE
  · -- everything is trivial
    have hsub : ∀ M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ, M = 0 := fun M =>
      Subsingleton.elim _ _
    have hsubB : ∀ M : Matrix (Fin n) (Fin n) ℝ, M = 0 := fun M => by
      have : IsEmpty (Fin n) := ⟨fun i => hE.false (Sum.inl i)⟩
      exact Subsingleton.elim _ _
    have hsubC : ∀ M : Matrix (Fin m) (Fin m) ℝ, M = 0 := fun M => by
      have : IsEmpty (Fin m) := ⟨fun i => hE.false (Sum.inr i)⟩
      exact Subsingleton.elim _ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsub (γ ^ 2 • (a * Sigma * a))]; exact Matrix.PosSemidef.zero
    · have := hsubB (Matrix.toBlocks₁₁ (γ ^ 2 • (a * Sigma * a)))
      rw [this]; exact Matrix.PosSemidef.zero
    · have := hsubC (Matrix.toBlocks₂₂ (γ ^ 2 • (a * Sigma * a)))
      rw [this]; exact Matrix.PosSemidef.zero
    · simp [Matrix.trace, Finset.univ_eq_empty]; positivity
    · rw [hsub (γ ^ 2 • (a * Sigma * a) - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ))]
      exact Matrix.PosSemidef.zero
  have hγ0 : 0 ≤ γ := by
    obtain ⟨i⟩ := hNE
    have h1 := hγ.diag_pos (i := i)
    have h2 := hD.diag_nonneg (i := i)
    rw [hAdef] at h1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    linarith
  -- the matrix L
  have hLpsd : (γ ^ 2 • (a * Sigma * a)).PosSemidef := by
    have := hSigma.posSemidef.conjTranspose_mul_mul_same a
    have h2 : aᴴ = a := by simpa using haT
    rw [h2] at this
    exact this.smul (sq_nonneg γ)
  -- square root of Sigma
  obtain ⟨Sq, hSq, hSqSq⟩ := psd_exists_sqrt Sigma hSigma.posSemidef
  have hSqT : Sqᵀ = Sq := by simpa using hSq.isHermitian.eq
  have hpsdSq : WassersteinDRO.Shrinkage.psdSqrt Sigma = Sq := psdSqrt_unique _ _ hSq hSqSq
  -- Y
  have hYpsd : (γ • (Sq * a * Sq)).PosSemidef := by
    have := hapd.posSemidef.conjTranspose_mul_mul_same Sq
    have h2 : Sqᴴ = Sq := by simpa using hSqT
    rw [h2] at this
    exact this.smul hγ0
  have hYY : (γ • (Sq * a * Sq)) * (γ • (Sq * a * Sq)) =
      WassersteinDRO.Shrinkage.psdSqrt Sigma * (γ ^ 2 • (a * Sigma * a)) *
        WassersteinDRO.Shrinkage.psdSqrt Sigma := by
    rw [hpsdSq]
    conv_rhs => rw [← hSqSq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    congr 1
    simp only [Matrix.mul_assoc]
  have hsqrtW : WassersteinDRO.Shrinkage.psdSqrt
      (WassersteinDRO.Shrinkage.psdSqrt Sigma * (γ ^ 2 • (a * Sigma * a)) *
        WassersteinDRO.Shrinkage.psdSqrt Sigma) = γ • (Sq * a * Sq) :=
    psdSqrt_unique _ _ hYpsd hYY
  refine ⟨hLpsd, hLpsd.submatrix Sum.inl, hLpsd.submatrix Sum.inr, ?_, ?_⟩
  · rw [hsqrtW]
    have hY1 : (Sq * a * Sq).trace = (a * Sigma).trace := by
      calc (Sq * a * Sq).trace = (Sq * (a * Sq)).trace := by rw [Matrix.mul_assoc]
        _ = ((a * Sq) * Sq).trace := Matrix.trace_mul_comm _ _
        _ = (a * Sigma).trace := by rw [Matrix.mul_assoc, hSqSq]
    have hL1 : (γ ^ 2 • (a * Sigma * a)).trace = γ ^ 2 * (Sigma * (a * a)).trace := by
      rw [Matrix.trace_smul, smul_eq_mul]
      congr 1
      calc (a * Sigma * a).trace = (a * (Sigma * a)).trace := by rw [Matrix.mul_assoc]
        _ = ((Sigma * a) * a).trace := Matrix.trace_mul_comm _ _
        _ = (Sigma * (a * a)).trace := by rw [Matrix.mul_assoc]
    have hsq : ((1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - γ • a) ^ 2 =
        1 - (2 * γ) • a + (γ ^ 2) • (a * a) := by
      simp only [sq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      module
    rw [hSigT, hsq] at hh
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hh
    have hS2 : (Sigma * a).trace = (a * Sigma).trace := Matrix.trace_mul_comm _ _
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hY1, hL1]
    rw [hS2] at hh
    nlinarith [hh]
  · -- L - σ I ⪰ 0
    have hE : (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)).PosSemidef := by
      apply psd_commute_mul _ _ hD
      · have h1 : ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D) =
            γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) + A := by
          rw [hAdef]; module
        rw [h1]
        exact ((Matrix.PosSemidef.one).smul hγ0).add hγ.posSemidef
      · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.one_mul]
    have hE2 : D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D) =
        γ ^ 2 • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - A * A := by
      rw [hAdef]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, smul_smul]
      module
    have haEa : a * (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)) * a =
        γ ^ 2 • (a * a) - 1 := by
      rw [hE2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      have : a * (A * A) * a = 1 := by
        calc a * (A * A) * a = (a * A) * (A * a) := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [haA, hAa, Matrix.one_mul]
      rw [this]
    have h2 : aᴴ = a := by simpa using haT
    have hP1 : (a * (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)) * a).PosSemidef := by
      have := hσ.conjTranspose_mul_mul_same a
      rwa [h2] at this
    have hP2 : (a * (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)) * a).PosSemidef := by
      have := hE.conjTranspose_mul_mul_same a
      rwa [h2] at this
    have hsplit : γ ^ 2 • (a * Sigma * a) - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) =
        γ ^ 2 • (a * (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)) * a) +
          σ • (a * (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)) * a) := by
      rw [haEa]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul]
      module
    rw [hsplit]
    exact (hP1.smul (sq_nonneg γ)).add (hP2.smul hσpos)

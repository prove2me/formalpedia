-- Prove2me | solution 1 for WassKF.Bisect.suboptimality_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:15:43.005922+00:00
-- url     : https://prove2.me/submissions/a3231753-6436-41cf-a035-0a28a7c3cc04

import Mathlib
import Definitions.Def_WassKF_Bisect_hFun
import Definitions.Def_WassKF_Bisect_Lgamma

set_option autoImplicit false

open Matrix

open scoped IsMulCommutative in
lemma comm_identity {𝒜 : Type*} [Ring 𝒜] [Algebra ℝ 𝒜] (D a b : 𝒜) (g gs : ℝ)
    (hDa : D * a = a * D) (hDb : D * b = b * D) (hab : a * b = b * a)
    (r1 : a * (g • (1 : 𝒜) - D) = 1) (r2 : b * (gs • (1 : 𝒜) - D) = 1) :
    g • (D * D * (b * b)) - g • (1 : 𝒜) + (g ^ 2) • a - (gs ^ 2) • (D * (b * b))
      - ((g - gs) ^ 2) • (D * D * a * (b * b)) = 0 := by
  have hc : ∀ x ∈ ({D, a, b} : Set 𝒜), ∀ y ∈ ({D, a, b} : Set 𝒜), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | assumption | exact (by assumption : _ = _).symm
  have hmc := Algebra.isMulCommutative_adjoin ℝ hc
  set K := Algebra.adjoin ℝ ({D, a, b} : Set 𝒜)
  let D' : K := ⟨D, Algebra.subset_adjoin (by simp)⟩
  let a' : K := ⟨a, Algebra.subset_adjoin (by simp)⟩
  let b' : K := ⟨b, Algebra.subset_adjoin (by simp)⟩
  have r1' : a' * (algebraMap ℝ K g - D') = 1 := by
    apply Subtype.ext
    simpa [D', a', Algebra.algebraMap_eq_smul_one] using r1
  have r2' : b' * (algebraMap ℝ K gs - D') = 1 := by
    apply Subtype.ext
    simpa [D', b', Algebra.algebraMap_eq_smul_one] using r2
  have key : algebraMap ℝ K g * (D' * D' * (b' * b')) - algebraMap ℝ K g
      + (algebraMap ℝ K g) ^ 2 * a' - (algebraMap ℝ K gs) ^ 2 * (D' * (b' * b'))
      - (algebraMap ℝ K (g - gs)) ^ 2 * (D' * D' * a' * (b' * b')) = 0 := by
    simp only [map_sub]
    linear_combination
      (-D' ^ 3 * b' ^ 2 - D' ^ 2 * b' ^ 2 * algebraMap ℝ K g + 2 * D' ^ 2 * b' ^ 2 * algebraMap ℝ K gs + D' + algebraMap ℝ K g) * r1'
      + (D' ^ 3 * a' * b' - D' ^ 2 * a' * b' * algebraMap ℝ K gs - D' ^ 2 * a' + D' ^ 2 * b' - D' * b' * algebraMap ℝ K gs - D') * r2'
  have := congrArg Subtype.val key
  simpa [D', a', b', Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, pow_two, smul_smul] using this

open scoped IsMulCommutative in
lemma comm3 {𝒜 : Type*} [Ring 𝒜] [Algebra ℝ 𝒜] (D a b : 𝒜)
    (hDa : D * a = a * D) (hDb : D * b = b * D) (hab : a * b = b * a) :
    D * D * a * (b * b) = (D * b) * a * (D * b) := by
  have hc : ∀ x ∈ ({D, a, b} : Set 𝒜), ∀ y ∈ ({D, a, b} : Set 𝒜), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | assumption | exact (by assumption : _ = _).symm
  have hmc := Algebra.isMulCommutative_adjoin ℝ hc
  set K := Algebra.adjoin ℝ ({D, a, b} : Set 𝒜)
  let D' : K := ⟨D, Algebra.subset_adjoin (by simp)⟩
  let a' : K := ⟨a, Algebra.subset_adjoin (by simp)⟩
  let b' : K := ⟨b, Algebra.subset_adjoin (by simp)⟩
  have key : D' * D' * a' * (b' * b') = (D' * b') * a' * (D' * b') := by ring
  have := congrArg Subtype.val key
  simpa [D', a', b'] using this

section psd
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma psd_exists_sqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) : ∃ S : Matrix n n ℝ, S.PosSemidef ∧ S * S = A := by
  have h0 : (0 : Matrix n n ℝ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  exact ⟨CFC.sqrt A, Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A),
    CFC.sqrt_mul_sqrt_self A h0⟩

end psd

lemma trace_mul_nonneg' {n : Type*} [Fintype n] [DecidableEq n] (S X : Matrix n n ℝ)
    (hS : S.PosSemidef) (hX : X.PosSemidef) : 0 ≤ (S * X).trace := by
  obtain ⟨R, hR, hRR⟩ := psd_exists_sqrt S hS
  have h1 : (S * X).trace = (Rᴴ * X * R).trace := by
    rw [← hRR, Matrix.mul_assoc, Matrix.trace_mul_comm, hR.isHermitian.eq, Matrix.mul_assoc]
  rw [h1]
  exact (hX.conjTranspose_mul_mul_same R).trace_nonneg


open WassKF.Bisect

theorem solution {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (γstar : ℝ)
    (hγstar : (γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (hroot : hFun Sigma D ρ γstar = 0)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef) :
    ((Lgamma Sigma D γstar - Lgamma Sigma D γ)ᵀ * D).trace ≤
      γ * (ρ ^ 2 - Sigma.trace) +
        γ ^ 2 * (((γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)⁻¹)ᵀ * Sigma).trace -
        ((Lgamma Sigma D γ)ᵀ * D).trace := by
  classical
  unfold hFun at hroot
  unfold Lgamma
  have hSigT : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hDT : Dᵀ = D := by simpa using hD.isHermitian.eq
  obtain ⟨A, hAdef⟩ : ∃ A, A = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D := ⟨_, rfl⟩
  rw [← hAdef] at hγ ⊢
  rw [← hBdef] at hγstar hroot ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = A⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = B⁻¹ := ⟨_, rfl⟩
  rw [← ha] at ⊢
  rw [← hb] at ⊢ hroot
  have hAT : Aᵀ = A := by rw [hAdef]; simp [hDT]
  have hBT : Bᵀ = B := by rw [hBdef]; simp [hDT]
  have hAu : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hγ.isUnit
  have hBu : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hγstar.isUnit
  have hAa : A * a = 1 := by rw [ha]; exact Matrix.mul_nonsing_inv _ hAu
  have haA : a * A = 1 := by rw [ha]; exact Matrix.nonsing_inv_mul _ hAu
  have hBb : B * b = 1 := by rw [hb]; exact Matrix.mul_nonsing_inv _ hBu
  have hbB : b * B = 1 := by rw [hb]; exact Matrix.nonsing_inv_mul _ hBu
  have haT : aᵀ = a := by rw [ha, Matrix.transpose_nonsing_inv, hAT]
  have hbT : bᵀ = b := by rw [hb, Matrix.transpose_nonsing_inv, hBT]
  have hDA : D = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - A := by
    rw [hAdef, sub_sub_cancel]
  have hDB : D = γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - B := by
    rw [hBdef, sub_sub_cancel]
  have hDa : D * a = a * D := by
    rw [hDA, Matrix.sub_mul, Matrix.mul_sub, hAa, haA]; simp
  have hDb : D * b = b * D := by
    rw [hDB, Matrix.sub_mul, Matrix.mul_sub, hBb, hbB]; simp
  have hABc : A * B = B * A := by
    rw [hAdef, hBdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
    module
  have hab : a * b = b * a := by
    have h1 : (A * B)⁻¹ = b * a := by rw [Matrix.mul_inv_rev, ha, hb]
    have h2 : (B * A)⁻¹ = a * b := by rw [Matrix.mul_inv_rev, ha, hb]
    rw [← h2, ← h1, hABc]
  have r1 : a * (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D) = 1 := by
    rw [← hAdef]; exact haA
  have r2 : b * (γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D) = 1 := by
    rw [← hBdef]; exact hbB
  have I1 := comm_identity D a b γ γstar hDa hDb hab r1 r2
  -- (1 - γstar • b) = -(D * b)
  have h1b : (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - γstar • b = -(D * b) := by
    have : b * (γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D) = 1 := r2
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at this
    rw [hDb, ← this]; abel
  have hsq : ((1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - γstar • b) ^ 2 = D * D * (b * b) := by
    rw [h1b, sq, neg_mul_neg]
    calc D * b * (D * b) = D * (b * D) * b := by simp only [Matrix.mul_assoc]
      _ = D * (D * b) * b := by rw [hDb]
      _ = D * D * (b * b) := by simp only [Matrix.mul_assoc]
  rw [hSigT, hsq] at hroot
  have hρ2 : ρ ^ 2 = (Sigma * (D * D * (b * b))).trace := by linarith
  -- positivity of the remainder
  have hapd : a.PosDef := by rw [ha]; exact hγ.inv
  have hCT : (D * b)ᵀ = D * b := by rw [Matrix.transpose_mul, hbT, hDT, ← hDb]
  have hNpsd : (D * D * a * (b * b)).PosSemidef := by
    rw [comm3 D a b hDa hDb hab]
    have := hapd.posSemidef.conjTranspose_mul_mul_same (D * b)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hCT] using this
  have hN : 0 ≤ (Sigma * (D * D * a * (b * b))).trace :=
    trace_mul_nonneg' _ _ hSigma.posSemidef hNpsd
  -- trace of I1
  have hI1 := congrArg (fun X => (Sigma * X).trace) I1
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul, Matrix.mul_zero, Matrix.trace_zero, smul_eq_mul] at hI1
  -- the two traces
  have hX : ((γstar ^ 2 • (b * Sigma * b) - γ ^ 2 • (a * Sigma * a))ᵀ * D).trace =
      γstar ^ 2 * (Sigma * (D * (b * b))).trace - γ ^ 2 * (a * Sigma * a * D).trace := by
    have e1 : (b * Sigma * b)ᵀ = b * Sigma * b := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hbT, hSigT, Matrix.mul_assoc]
    have e2 : (a * Sigma * a)ᵀ = a * Sigma * a := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, haT, hSigT, Matrix.mul_assoc]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, e1, e2, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul]
    congr 2
    -- tr(b Σ b D) = tr(Σ (D (b b)))
    calc (b * Sigma * b * D).trace = (b * (Sigma * b * D)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Sigma * b * D) * b).trace := Matrix.trace_mul_comm _ _
      _ = (Sigma * (D * (b * b))).trace := by
          have : b * D = D * b := hDb.symm
          calc ((Sigma * b * D) * b).trace = (Sigma * (b * D * b)).trace := by
                simp only [Matrix.mul_assoc]
            _ = (Sigma * (D * (b * b))).trace := by
                rw [this]; simp only [Matrix.mul_assoc]
  have hY : (((γ ^ 2 • (a * Sigma * a))ᵀ * D)).trace = γ ^ 2 * (a * Sigma * a * D).trace := by
    have e2 : (a * Sigma * a)ᵀ = a * Sigma * a := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, haT, hSigT, Matrix.mul_assoc]
    rw [Matrix.transpose_smul, e2, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hZ : (aᵀ * Sigma).trace = (Sigma * a).trace := by
    rw [haT, Matrix.trace_mul_comm]
  rw [hX, hY, hZ, hρ2]
  have hδ : 0 ≤ (γ - γstar) ^ 2 * (Sigma * (D * D * a * (b * b))).trace :=
    mul_nonneg (sq_nonneg _) hN
  nlinarith [hδ, hI1]

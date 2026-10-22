-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P26.identity_success_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:34:44.336685+00:00
-- url     : https://prove2.me/submissions/fd1d2681-2041-4f86-83d4-cbb8a6e7b675

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26
noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)


open QAlgorithms

lemma g67g_tr_le {ι : Type} [Fintype ι] [DecidableEq ι] (M ρ : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hρ : IsDensityMatrix ρ) :
    (M * ρ).trace.re ≤ M.trace.re := by
  have hH := hρ.1.isHermitian
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hspec : ρ = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have h1 := hH.trace_eq_sum_eigenvalues
    rw [hρ.2] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    exact h2.symm
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hρ.1.eigenvalues_nonneg j) (Finset.mem_univ i)
  set lam := hH.eigenvalues with hlam
  clear_value lam U
  set C : Matrix ι ι ℂ := U * Matrix.diagonal (fun i => ((Real.sqrt (1 - lam i) : ℝ) : ℂ))
  have hC : 1 - ρ = C * Cᴴ := by
    have hd : Matrix.diagonal (fun i => ((Real.sqrt (1 - lam i) : ℝ) : ℂ)) *
        (Matrix.diagonal (fun i => ((Real.sqrt (1 - lam i) : ℝ) : ℂ)))ᴴ =
        1 - Matrix.diagonal (RCLike.ofReal ∘ lam) := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq, Pi.star_apply,
          Function.comp_apply, RCLike.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [hle i])]
        simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    simp only [C, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal _), hd, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      ← Matrix.star_eq_conjTranspose, hUU, hspec, Matrix.mul_assoc]
  clear_value C
  have h0 : 0 ≤ (M * (1 - ρ)).trace.re := by
    rw [hC, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    have := (hM.mul_mul_conjTranspose_same Cᴴ).trace_nonneg
    rw [Matrix.conjTranspose_conjTranspose] at this
    rw [← Matrix.mul_assoc]
    exact (Complex.nonneg_iff.mp this).1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at h0
  linarith

/-- PDF p.1, unnumbered identity-channel calculation: arbitrary mixed, possibly
entangled n-qubit codewords, every decoder, and uniform integer message count.
Includes n=0, when success is at most 1/M. -/
theorem solution (n M : ℕ) (hM : 0 < M)
    (K : UACode (Fin n → Fin 2) (Fin n → Fin 2) M) :
    uaCodeSuccess (fun X => X) K ≤ (2 : ℝ)^n / M := by
  unfold uaCodeSuccess
  have hsum : ∑ k, effectProb (K.measurement k) (K.state k) ≤ (2 : ℝ) ^ n := by
    calc ∑ k, effectProb (K.measurement k) (K.state k)
        ≤ ∑ k, (K.measurement k).trace.re :=
          Finset.sum_le_sum (fun k _ => g67g_tr_le _ _ (K.povm.1 k) (K.density k))
      _ = (2 : ℝ) ^ n := by
          rw [← Complex.re_sum, ← Matrix.trace_sum, K.povm.2, Matrix.trace_one]
          simp
          rw [show ((2:ℂ)^n) = (((2:ℝ)^n : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hMpos.le)


end

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P03.localUnitaryInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:05:01.059015+00:00
-- url     : https://prove2.me/submissions/c12da669-73e7-4246-b6cd-d3ad4888a221

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq


theorem g73j_kron_conj {d : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (U : Matrix (Fin d) (Fin d) ℂ) (M : Matrix (Fin d × A) (Fin d × A) ℂ) (a b : Fin d) (x y : A) :
    conjSuperop (Matrix.kronecker U (1 : Matrix A A ℂ)) M (a, x) (b, y) =
      ∑ a', ∑ b', U a a' * M (a', x) (b', y) * starRingEnd ℂ (U b b') := by
  simp only [conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, RCLike.star_def]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  simp only [ite_mul, zero_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_comm

theorem g73j_eig_conj {I : Type} [Fintype I] [DecidableEq I] (W X : Matrix I I ℂ) (hW : Wᴴ * W = 1) :
    ascEigenvalues (W * X * Wᴴ) = ascEigenvalues X := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  unfold ascEigenvalues
  by_cases hX : X.IsHermitian
  · have hY : (W * X * Wᴴ).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX.eq,
        Matrix.mul_assoc]
    rw [dif_pos hX, dif_pos hY]
    have hc : (W * X * Wᴴ).charpoly = X.charpoly := by
      rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]
    have : hY.eigenvalues₀ = hX.eigenvalues₀ := by
      apply List.ofFn_injective
      rw [← hY.sort_roots_charpoly_eq_eigenvalues₀, ← hX.sort_roots_charpoly_eq_eigenvalues₀, hc]
    rw [this]
  · have hY : ¬ (W * X * Wᴴ).IsHermitian := by
      intro hY; apply hX
      have : Wᴴ * (W * X * Wᴴ) * W = X := by
        rw [show Wᴴ * (W * X * Wᴴ) * W = (Wᴴ * W) * X * (Wᴴ * W) by simp only [← Matrix.mul_assoc],
          hW, Matrix.one_mul, Matrix.mul_one]
      rw [← this]; unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hY.eq]
      simp only [Matrix.mul_assoc]
    rw [dif_neg hX, dif_neg hY]

theorem g73j_schatten_conj {I : Type} [Fintype I] [DecidableEq I] (W X : Matrix I I ℂ) (hW : Wᴴ * W = 1)
    (p : ℝ) : schatten p (conjSuperop W X) = schatten p X := by
  unfold schatten QAlgorithms.Papers.Independent.Information100.P63.eigen conjSuperop
  rw [g73j_eig_conj W X hW]

theorem g73j_depol_cov (d : ℕ) (q : ℝ) (U Z : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    QAlgorithms.Papers.Independent.Information100.P08.depolarizing d q (conjSuperop U Z) =
      conjSuperop U (QAlgorithms.Papers.Independent.Information100.P08.depolarizing d q Z) := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have htr : (U * Z * Uᴴ).trace = Z.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp only [conjSuperop, QAlgorithms.Papers.Independent.Information100.P08.depolarizing,
    QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed, htr, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']

theorem g73j_kraus_lin {A B K : Type} [Fintype A] [Fintype B] [Fintype K] {m : Type} [Fintype m]
    (E : K → Matrix B A ℂ) (c : m → m → ℂ) (Z : m → m → Matrix A A ℂ) :
    krausApply E (∑ a, ∑ b, c a b • Z a b) = ∑ a, ∑ b, c a b • krausApply E (Z a b) := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]

theorem g73j_conj_entry {d : ℕ} (U Z : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    conjSuperop U Z i j = ∑ a', ∑ b', U i a' * Z a' b' * starRingEnd ℂ (U j b') := by
  simp only [conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem g73j_local {d : ℕ} {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (q : ℝ) (Psi : Superop A B) (hPsi : IsChannel Psi)
    (rho : Matrix (Fin d × A) (Fin d × A) ℂ) (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    productChannel (QAlgorithms.Papers.Independent.Information100.P08.depolarizing d q) Psi
      (conjSuperop (Matrix.kronecker U (1 : Matrix A A ℂ)) rho) =
    conjSuperop (Matrix.kronecker U (1 : Matrix B B ℂ))
      (productChannel (QAlgorithms.Papers.Independent.Information100.P08.depolarizing d q) Psi rho) := by
  obtain ⟨n, E, _, hE⟩ := hPsi
  ext ⟨a, x⟩ ⟨b, y⟩
  rw [g73j_kron_conj]
  -- block of the inner output
  have hblk : (Matrix.of fun i j => idTensorSuperop Psi
      (conjSuperop (Matrix.kronecker U (1 : Matrix A A ℂ)) rho) (i, x) (j, y)) =
      conjSuperop U (Matrix.of fun i j => idTensorSuperop Psi rho (i, x) (j, y)) := by
    ext i j
    rw [g73j_conj_entry]
    simp only [Matrix.of_apply, idTensorSuperop, hE]
    have hZ : (Matrix.of fun k k' => conjSuperop (Matrix.kronecker U (1 : Matrix A A ℂ)) rho (i, k) (j, k'))
        = ∑ a', ∑ b', (U i a' * starRingEnd ℂ (U j b')) •
          (Matrix.of fun k k' => rho (a', k) (b', k')) := by
      ext k k'
      simp only [Matrix.of_apply, g73j_kron_conj, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl; intro a' _; apply Finset.sum_congr rfl; intro b' _; ring
    rw [hZ, g73j_kraus_lin]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro a' _; apply Finset.sum_congr rfl; intro b' _; ring
  have hL : productChannel (QAlgorithms.Papers.Independent.Information100.P08.depolarizing d q) Psi
      (conjSuperop (Matrix.kronecker U (1 : Matrix A A ℂ)) rho) (a, x) (b, y) =
      QAlgorithms.Papers.Independent.Information100.P08.depolarizing d q
        (Matrix.of fun i j => idTensorSuperop Psi
          (conjSuperop (Matrix.kronecker U (1 : Matrix A A ℂ)) rho) (i, x) (j, y)) a b := rfl
  rw [hL, hblk, g73j_depol_cov d q U _ hU, g73j_conj_entry]
  rfl

theorem g73j_kron_unitary {d : ℕ} {B : Type} [Fintype B] [DecidableEq B]
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    (Matrix.kronecker U (1 : Matrix B B ℂ))ᴴ * Matrix.kronecker U (1 : Matrix B B ℂ) = 1 := by
  unfold Matrix.kronecker
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, hU,
    Matrix.one_mul, Matrix.one_kronecker_one]

/-- King quant-ph/0204172v2, PDF p.10, Lemma 7, (31).
The local input unitary is arbitrary; no diagonal-marginal assumption is present. -/
theorem solution {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (Psi : Superop A B) (hPsi : IsChannel Psi)
    (rho : Matrix (Fin d × A) (Fin d × A) ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (p : ℝ) (hp : 1 ≤ p) :
    schatten p (productChannel (depolarizing d (1 - lam)) Psi rho) =
      schatten p (productChannel (depolarizing d (1 - lam)) Psi
        (conjSuperop (Matrix.kronecker (U : Matrix (Fin d) (Fin d) ℂ) (1 : Matrix A A ℂ)) rho)) := by
  have hU : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * (U : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    have := U.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  rw [g73j_local (1 - lam) Psi hPsi rho _ hU, g73j_schatten_conj _ _ (g73j_kron_unitary _ hU)]



end

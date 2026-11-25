-- Prove2me | solution 1 for WeilConjectures.exists_matrix_data_of_trace_formula_of_isPerfPair
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-25T12:55:37.815577+00:00
-- url     : https://prove2.me/submissions/248cf1e4-1ecb-4d58-9e54-e8754257e3f2

import Mathlib

/-- Solution of `WeilConjectures.exists_matrix_data_of_trace_formula_of_isPerfPair`: choose bases, take the
matrices of the endomorphisms and the Gram matrices of the perfect pairings. -/
theorem solution {K : Type*} [Field K] (n : ℕ)
    (V : ℕ → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, V i →ₗ[K] V i) (N : ℕ → K) (c : K)
    (htr : ∀ m, 1 ≤ m → N m =
      ∑ i ∈ Finset.range (2 * n + 1), (-1) ^ i * LinearMap.trace K (V i) (F i ^ m))
    (pair : ∀ i, V i →ₗ[K] V (2 * n - i) →ₗ[K] K)
    (hperf : ∀ i ≤ 2 * n, (pair i).IsPerfPair)
    (hsim : ∀ i ≤ 2 * n, ∀ x y, pair i (F i x) (F (2 * n - i) y) = c * pair i x y) :
    ∃ (d : ℕ → ℕ) (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K),
      (∀ m : ℕ, 0 < m → N m =
        ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace) ∧
      (∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
          (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
          G * H = 1 ∧ H * G = 1 ∧ (Φ i).transpose * G * Φ (2 * n - i) = c • G) := by
  classical
  let b : ∀ i, Module.Basis (Fin (Module.finrank K (V i))) K (V i) := fun i => Module.finBasis K (V i)
  refine ⟨fun i => Module.finrank K (V i), fun i => LinearMap.toMatrix (b i) (b i) (F i), ?_, ?_⟩
  · intro m hm
    rw [htr m hm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace]
  · intro i hi
    have := hperf i hi
    let e : V i ≃ₗ[K] Module.Dual K (V (2 * n - i)) :=
      LinearEquiv.ofBijective (pair i) (LinearMap.IsPerfPair.bijective_left (pair i))
    let M := LinearMap.toMatrix (b i) (b (2 * n - i)).dualBasis (e : V i →ₗ[K] Module.Dual K (V (2 * n - i)))
    let M' := LinearMap.toMatrix (b (2 * n - i)).dualBasis (b i)
      (e.symm : Module.Dual K (V (2 * n - i)) →ₗ[K] V i)
    have hMM' : M * M' = 1 := by
      simp only [M, M']
      rw [← LinearMap.toMatrix_comp]
      have : (e : V i →ₗ[K] Module.Dual K (V (2 * n - i))).comp
          (e.symm : Module.Dual K (V (2 * n - i)) →ₗ[K] V i) = LinearMap.id := by
        ext φ x; simp
      rw [this, LinearMap.toMatrix_id]
    have hM'M : M' * M = 1 := by
      simp only [M, M']
      rw [← LinearMap.toMatrix_comp]
      have : (e.symm : Module.Dual K (V (2 * n - i)) →ₗ[K] V i).comp
          (e : V i →ₗ[K] Module.Dual K (V (2 * n - i))) = LinearMap.id := by
        ext x; simp
      rw [this, LinearMap.toMatrix_id]
    have hG : LinearMap.toMatrix₂ (b i) (b (2 * n - i)) (pair i) = M.transpose := by
      ext a a'
      simp [M, e, LinearMap.toMatrix₂_apply, LinearMap.toMatrix_apply]
    refine ⟨M.transpose, M'.transpose, ?_, ?_, ?_⟩
    · rw [← Matrix.transpose_mul, hM'M, Matrix.transpose_one]
    · rw [← Matrix.transpose_mul, hMM', Matrix.transpose_one]
    · rw [← hG, ← LinearMap.toMatrix₂_compl₁₂]
      have hc : (pair i).compl₁₂ (F i) (F (2 * n - i)) = c • pair i := by
        ext x y
        simp [hsim i hi]
      rw [hc, map_smul]


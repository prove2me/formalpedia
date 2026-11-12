-- Prove2me | solution 1 for QAlgorithms.Nannicini.densityMatrix_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:15:43.248203+00:00
-- url     : https://prove2.me/submissions/7b979f16-a58f-474b-a988-c354991d907c

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

open QAlgorithms
open scoped BigOperators ComplexOrder




open QAlgorithms

open scoped ComplexOrder


/-- Nannicini p.36, Theorem 1.60 (characterization of density matrices): a `q`-qubit matrix `ρ`
is the density matrix `∑_j p_j |ψ_j⟩⟨ψ_j|` of some ensemble `{p_j, |ψ_j⟩}_{j=1..m}` of pure
states (unit vectors) with probabilities `p_j ≥ 0`, `∑_j p_j = 1`, for some `m`, if and only if
`ρ` has unit trace and is positive semidefinite. -/
theorem solution {q : ℕ} (ρ : Matrix (Qubits q) (Qubits q) ℂ) :
    (∃ (m : ℕ) (p : Fin m → ℝ) (ψ : Fin m → EuclideanSpace ℂ (Qubits q)),
        (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧ (∀ j, IsState (ψ j)) ∧ ρ = ensembleDensity p ψ) ↔
      ρ.trace = 1 ∧ ρ.PosSemidef := by
  classical
  have htr (v : EuclideanSpace ℂ (Qubits q)) :
      (pureDensity v).trace = (‖v‖ : ℂ) ^ 2 := by
    calc
      (pureDensity v).trace = ∑ i, v i * star (v i) := rfl
      _ = inner ℂ v v := rfl
      _ = (‖v‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K v
  have hpos (v : EuclideanSpace ℂ (Qubits q)) : (pureDensity v).PosSemidef := by
    change (Matrix.vecMulVec (v : Qubits q → ℂ) (star (v : Qubits q → ℂ))).PosSemidef
    exact Matrix.posSemidef_vecMulVec_self_star _
  constructor
  · rintro ⟨m, p, ψ, hp, hpSum, hψ, rfl⟩
    have hn : ∀ j, ‖ψ j‖ = 1 := hψ
    constructor
    · calc
        (ensembleDensity p ψ).trace = ∑ j, (p j : ℂ) := by
          simp [ensembleDensity, Matrix.trace_sum, Matrix.trace_smul, htr, hn]
        _ = 1 := by exact_mod_cast hpSum
    · unfold ensembleDensity
      apply Matrix.posSemidef_sum Finset.univ
      intro j hj
      exact (hpos (ψ j)).smul (Complex.zero_le_real.mpr (hp j))
  · rintro ⟨htrace, hρ⟩
    let hH := hρ.isHermitian
    let e : Fin (Fintype.card (Qubits q)) ≃ Qubits q := (Fintype.equivFin _).symm
    have hsum : (∑ i, hH.eigenvalues i) = (1 : ℝ) := by
      have ht := congrArg Complex.re hH.trace_eq_sum_eigenvalues
      simpa [htrace] using ht.symm
    refine ⟨Fintype.card (Qubits q), (fun j => hH.eigenvalues (e j)),
      (fun j => hH.eigenvectorBasis (e j)), ?_, ?_, ?_, ?_⟩
    · intro j
      exact hρ.eigenvalues_nonneg (e j)
    · rw [e.sum_comp]
      exact hsum
    · intro j
      exact hH.eigenvectorBasis.orthonormal.norm_eq_one (e j)
    · change ρ = ∑ j, (hH.eigenvalues (e j) : ℂ) • pureDensity (hH.eigenvectorBasis (e j))
      rw [e.sum_comp (fun i => (hH.eigenvalues i : ℂ) • pureDensity (hH.eigenvectorBasis i))]
      conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
      ext i j
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Function.comp_apply, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, pureDensity, Matrix.of_apply,
        starRingEnd_apply]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [RCLike.ofReal_eq_complex_ofReal]
      ac_rfl

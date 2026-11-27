-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.quantum_wellposed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:41:05.188428+00:00
-- url     : https://prove2.me/submissions/2e29d94b-e7c8-4ab9-a409-8b77c00e5389

import Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical.QWAux
open TFIMPhaseDiagram.Classical Matrix

lemma pauliEntry_star (P : Pauli) (x y : Bool) :
    star (pauliEntry P y x) = pauliEntry P x y := by
  cases P <;> cases x <;> cases y <;>
    simp [pauliEntry, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ]

lemma pauliString_isHermitian {n : ℕ} (P : Fin n → Pauli) : (pauliString P).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, pauliString, star_prod, pauliEntry_star]

lemma localZ_eq {n : ℕ} (i : Fin n) :
    localPauli .Z i = diagonal (fun a : Bits n => if a i then (-1 : ℂ) else 1) := by
  ext a b
  simp only [localPauli, pauliString, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    rw [Finset.prod_eq_single i]
    · simp [pauliEntry, QAlgorithms.pauliZ]
    · intro k _ hk; simp [hk, pauliEntry]
    · simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h; push Not at h; exact hab (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hki : k = i
    · simp [hki, pauliEntry, QAlgorithms.pauliZ, diagonal_apply]
      subst hki; simp [hk]
    · simp [hki, pauliEntry, hk]

lemma realSmul_sa {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℝ) (A : Matrix ι ι ℂ)
    (hA : IsSelfAdjoint A) : IsSelfAdjoint ((r : ℂ) • A) :=
  IsSelfAdjoint.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]) hA

lemma hamiltonian_isHermitian {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h η : Fin n → ℝ) :
    (hamiltonian J h η).IsHermitian := by
  have hd : ∀ i : Fin n, IsSelfAdjoint (localPauli .Z i) := fun i =>
    pauliString_isHermitian _
  have hzz : ∀ i j : Fin n, IsSelfAdjoint (localPauli .Z i * localPauli .Z j) := by
    intro i j
    rw [localZ_eq, localZ_eq, diagonal_mul_diagonal]
    apply isHermitian_diagonal_of_self_adjoint
    funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  have h1 : IsSelfAdjoint (hz J h) := by
    unfold hz
    refine IsSelfAdjoint.add ?_ ?_
    · have : (1 / 2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      apply realSmul_sa
      exact isSelfAdjoint_sum _ fun i _ => isSelfAdjoint_sum _ fun j _ => realSmul_sa _ _ (hzz i j)
    · exact isSelfAdjoint_sum _ fun i _ => realSmul_sa _ _ (hd i)
  have h2 : IsSelfAdjoint (hx η) :=
    isSelfAdjoint_sum _ fun i _ => realSmul_sa _ _ (pauliString_isHermitian _)
  exact h1.add h2

lemma cfc_exp_eq {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    cfc Real.exp A = NormedSpace.exp A := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  conv_rhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hinv : star U = U⁻¹ := (Matrix.inv_eq_left_inv hU1).symm
  have hunit : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_left_inverse hU1
  rw [hinv, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal]
  rw [Pi.exp_def]
  congr 2
  congr 1
  funext i
  simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

lemma trace_exp {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Matrix.trace (NormedSpace.exp A) = ((∑ i, Real.exp (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [← cfc_exp_eq A hA, hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  push_cast
  simp [Complex.ofReal_exp]


theorem qw {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) :
  (hamiltonian J h η).IsHermitian ∧ (partition J h η).im = 0 ∧
    0 < (partition J h η).re ∧ gibbsAdapter J h η = density J h η := by
  have hH := hamiltonian_isHermitian J h η
  have htr : partition J h η = ((∑ i, Real.exp (hH.eigenvalues i) : ℝ) : ℂ) := by
    unfold partition matrixExp; exact trace_exp _ hH
  have hpos : 0 < ∑ i, Real.exp (hH.eigenvalues i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  refine ⟨hH, by rw [htr]; simp, by rw [htr, Complex.ofReal_re]; exact hpos, ?_⟩
  have hham : RouzeFranca.LearnGibbs.hamiltonian (fun _ : Fin 1 => hamiltonian J h η)
      (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))) = hamiltonian J h η := by
    simp [RouzeFranca.LearnGibbs.hamiltonian]
  have hfun : (fun x : ℝ => Real.exp (-(-1 : ℝ) * x)) = Real.exp := by
    funext x; simp
  unfold gibbsAdapter RouzeFranca.LearnGibbs.gibbs RouzeFranca.LearnGibbs.partitionFn density
  rw [hham, hfun, cfc_exp_eq _ hH]
  have : Matrix.trace (NormedSpace.exp (hamiltonian J h η)) = partition J h η := rfl
  rw [this, htr]
  simp only [Complex.ofReal_re]
  push_cast
  rfl

end TFIMPhaseDiagram.Classical.QWAux

open TFIMPhaseDiagram.Classical in
theorem solution {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) :
  (hamiltonian J h η).IsHermitian ∧ (partition J h η).im = 0 ∧
    0 < (partition J h η).re ∧ gibbsAdapter J h η = density J h η :=
  TFIMPhaseDiagram.Classical.QWAux.qw hn J hJ h η

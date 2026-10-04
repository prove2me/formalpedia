-- Prove2me | solution 1 for UnQuantumMechanics.hamiltonian_matrices_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:22:25.273769+00:00
-- url     : https://prove2.me/submissions/a505cfd8-3e1e-411d-a77d-77d5a5b0b8b0

import Mathlib
import Definitions.Def_UnQM_phase_space

set_option autoImplicit false

namespace F4FC756A

open Matrix UnQuantumMechanics
open scoped Kronecker

lemma eta0_sq : eta0 * eta0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

lemma gamma0_sq (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  unfold gamma0
  change (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ eta0 * ((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ eta0) = -1
  rw [← Matrix.mul_kronecker_mul, eta0_sq, Matrix.one_mul]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : i = j <;> by_cases h2 : a = b <;> simp [h1, h2]

/-- The matrix attached to a function on `Sym2`. -/
def symMat (n : ℕ) (g : Sym2 (PhaseIdx n) → ℝ) : Matrix (PhaseIdx n) (PhaseIdx n) ℝ :=
  Matrix.of fun i j => g s(i, j)

/-- The linear map `g ↦ γ₀ * symMat g`. -/
def F (n : ℕ) : (Sym2 (PhaseIdx n) → ℝ) →ₗ[ℝ] Matrix (PhaseIdx n) (PhaseIdx n) ℝ where
  toFun g := gamma0 n * symMat n g
  map_add' g h := by
    rw [← Matrix.mul_add]; congr 1
  map_smul' c g := by
    simp only [RingHom.id_apply]
    rw [← Matrix.mul_smul]; congr 1

lemma F_inj (n : ℕ) : Function.Injective (F n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have h1 : symMat n g = 0 := by
    have h2 : gamma0 n * (gamma0 n * symMat n g) = 0 := by
      change gamma0 n * (F n g) = 0
      rw [hg, Matrix.mul_zero]
    rw [← Matrix.mul_assoc, gamma0_sq, Matrix.neg_mul, Matrix.one_mul, neg_eq_zero] at h2
    exact h2
  funext s
  induction s using Sym2.ind with
  | h i j =>
    have := congrFun (congrFun h1 i) j
    simpa [symMat] using this

lemma set_eq (n : ℕ) :
    {M | IsHamiltonianMatrix n M} = (LinearMap.range (F n) : Set _) := by
  ext M
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Sym2.lift ⟨fun i j => A i j, fun i j => (hA.apply i j).symm⟩, ?_⟩
    change gamma0 n * symMat n _ = _
    congr 1
  · rintro ⟨g, rfl⟩
    refine ⟨symMat n g, ?_, rfl⟩
    ext i j
    simp [symMat, Sym2.eq_swap]

lemma choose_eq (n : ℕ) : Nat.choose (n * 2 + 1) 2 = n * (2 * n + 1) := by
  rw [Nat.choose_two_right]
  have h : (n * 2 + 1) * (n * 2 + 1 - 1) = 2 * (n * (2 * n + 1)) := by
    rw [Nat.add_sub_cancel]; ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

end F4FC756A

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ {M | IsHamiltonianMatrix n M}) = n * (2 * n + 1) := by
  rw [F4FC756A.set_eq, Submodule.span_eq, LinearMap.finrank_range_of_inj (F4FC756A.F_inj n),
    Module.finrank_fintype_fun_eq_card, Sym2.card]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact F4FC756A.choose_eq n

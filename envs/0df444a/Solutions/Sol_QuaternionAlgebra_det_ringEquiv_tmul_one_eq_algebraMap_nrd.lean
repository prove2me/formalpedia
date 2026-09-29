-- Prove2me | solution 1 for QuaternionAlgebra.det_ringEquiv_tmul_one_eq_algebraMap_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/03b68f2b-4e1f-5747-ab96-003ddca5094e

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_det_ringEquiv_tmul_one_eq_algebraMap_nrd

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace DetNrdCC

section Quadratic

variable {R : Type*} [CommRing R] {a b : R}

theorem sq_sub_trd_smul_add_nrd (x : ℍ[R, a, b]) :
    x * x - QuaternionAlgebra.trd x • x + QuaternionAlgebra.nrd x • (1 : ℍ[R, a, b]) = 0 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  ext <;> simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

end Quadratic

section Matrices

variable {K : Type*} [Field K]

theorem mat_sq_sub_trace_smul_add_det (A : Matrix (Fin 2) (Fin 2) K) :
    A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem det_eq_or_exists_eq_smul_one (A : Matrix (Fin 2) (Fin 2) K) (t n : K)
    (h : A * A - t • A + n • (1 : Matrix (Fin 2) (Fin 2) K) = 0) :
    A.det = n ∨ ∃ κ : K, A = κ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 := mat_sq_sub_trace_smul_add_det A
  have h3 : (A.trace - t) • A = (A.det - n) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have := sub_eq_zero.2 (h.trans h2.symm)
    rw [sub_smul, sub_smul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    convert this using 1
    abel
  by_cases ht : A.trace = t
  · left
    rw [ht, sub_self, zero_smul] at h3
    have := congrFun (congrFun h3.symm 0) 0
    simp at this
    exact sub_eq_zero.1 this
  · right
    have hne : A.trace - t ≠ 0 := sub_ne_zero.2 ht
    have := congrArg (fun M => (A.trace - t)⁻¹ • M) h3
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    exact ⟨_, this⟩

end Matrices

section Chart

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] {a b : R}

theorem coords_of_tmul_one_eq_one_tmul (x : ℍ[R, a, b]) (κ : K)
    (h : x ⊗ₜ[R] (1 : K) = (1 : ℍ[R, a, b]) ⊗ₜ[R] κ) :
    algebraMap R K x.re = κ ∧ algebraMap R K x.imI = 0 ∧
      algebraMap R K x.imJ = 0 ∧ algebraMap R K x.imK = 0 := by
  have h' : ((1 : K) ⊗ₜ[R] x : K ⊗[R] ℍ[R, a, b]) = κ ⊗ₜ[R] (1 : ℍ[R, a, b]) := by
    have := congrArg (TensorProduct.comm R ℍ[R, a, b] K) h
    simpa [TensorProduct.comm_tmul] using this
  let B := Algebra.TensorProduct.basis K (QuaternionAlgebra.basisOneIJK (R := R) a 0 b)
  have hi : ∀ i : Fin 4, B.repr ((1 : K) ⊗ₜ[R] x) i = B.repr (κ ⊗ₜ[R] (1 : ℍ[R, a, b])) i :=
    fun i => by rw [h']
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  have h3 := hi 3
  simp only [B, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.coe_smul,
    Finsupp.mapRange_apply, Pi.smul_apply, QuaternionAlgebra.coe_basisOneIJK_repr,
    smul_eq_mul] at h0 h1 h2 h3
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem det_ringEquiv_tmul_one_eq (φ : ℍ[R, a, b] ⊗[R] K ≃+* Matrix (Fin 2) (Fin 2) K)
    (hφ : ∀ t : K, φ ((1 : ℍ[R, a, b]) ⊗ₜ[R] t) = t • (1 : Matrix (Fin 2) (Fin 2) K))
    (x : ℍ[R, a, b]) :
    (φ (x ⊗ₜ[R] (1 : K))).det = algebraMap R K (QuaternionAlgebra.nrd x) := by

  have hsmul : ∀ (r : R) (y : ℍ[R, a, b]),
      φ ((r • y) ⊗ₜ[R] (1 : K)) = algebraMap R K r • φ (y ⊗ₜ[R] (1 : K)) := fun r y => by
    have e1 : (r • y) ⊗ₜ[R] (1 : K) = y ⊗ₜ[R] (algebraMap R K r) := by
      rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    have e2 : (y ⊗ₜ[R] (algebraMap R K r) : ℍ[R, a, b] ⊗[R] K) =
        (y ⊗ₜ[R] (1 : K)) * ((1 : ℍ[R, a, b]) ⊗ₜ[R] (algebraMap R K r)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1, e2, map_mul, hφ, Matrix.mul_smul, mul_one]
  set A := φ (x ⊗ₜ[R] (1 : K)) with hA

  have hrel : A * A - algebraMap R K (QuaternionAlgebra.trd x) • A +
      algebraMap R K (QuaternionAlgebra.nrd x) • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
    have h0 := congrArg (fun y : ℍ[R, a, b] => φ (y ⊗ₜ[R] (1 : K))) (sq_sub_trd_smul_add_nrd x)
    rw [TensorProduct.add_tmul, TensorProduct.sub_tmul, map_add, map_sub, hsmul, hsmul,
      TensorProduct.zero_tmul, map_zero,
      show (x * x) ⊗ₜ[R] (1 : K) = (x ⊗ₜ[R] (1 : K)) * (x ⊗ₜ[R] (1 : K)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
      map_mul, hφ, one_smul] at h0
    exact h0

  rcases det_eq_or_exists_eq_smul_one A _ _ hrel with hdet | ⟨κ, hκ⟩
  · exact hdet
  ·
    have hx : x ⊗ₜ[R] (1 : K) = (1 : ℍ[R, a, b]) ⊗ₜ[R] κ :=
      φ.injective (by rw [← hA, hκ, hφ])
    obtain ⟨hre, hI, hJ, hK⟩ := coords_of_tmul_one_eq_one_tmul x κ hx
    rw [hκ, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, QuaternionAlgebra.nrd]
    simp only [map_add, map_sub, map_mul, map_pow, hre, hI, hJ, hK]
    ring

end Chart

end DetNrdCC

end

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

theorem solution
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ t : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (x : ℍ[ℚ, a, b]) :
    (φ (x ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))).det = algebraMap ℚ (v.adicCompletion ℚ) (QuaternionAlgebra.nrd x) :=
  DetNrdCC.det_ringEquiv_tmul_one_eq φ hφ x

end S_QuaternionAlgebra_det_ringEquiv_tmul_one_eq_algebraMap_nrd
end P2MW
export P2MW.S_QuaternionAlgebra_det_ringEquiv_tmul_one_eq_algebraMap_nrd (solution)

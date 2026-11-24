-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_normForm_eq_det_40a80ca110c3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:47.006802+00:00
-- url     : https://prove2.me/submissions/15e89195-af1c-480a-bb44-a5637e328405

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
open scoped TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
namespace GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) {n : ℕ} (x : Fin n → A) :
    normForm A x = Matrix.det (Matrix.of fun i k => ∑ j, X j * C (b.repr (x j * b k) i)) := by
  letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
    MvPolynomial.algebraMvPolynomial
  let e₀ : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[R] MvPolynomial (Fin n) A :=
    (Algebra.TensorProduct.comm R _ A).trans
      ((MvPolynomial.algebraTensorAlgEquiv R A).restrictScalars R)
  have he₀ : ∀ a : A, e₀ (1 ⊗ₜ a) = C a := by
    intro a; simp [e₀, MvPolynomial.smul_eq_C_mul]
  have he₁ : ∀ p, e₀ (p ⊗ₜ 1) = MvPolynomial.map (algebraMap R A) p := by
    intro p; simp [e₀]
  let e : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun p => by
      simp [Algebra.TensorProduct.algebraMap_apply, he₁])
  let B := (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map e.toLinearEquiv
  have hB : ∀ i, B i = C (b i) := by
    intro i
    simp only [B, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact he₀ (b i)
  unfold normForm
  rw [Algebra.norm_eq_matrix_det B]
  congr 1
  ext i k
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.of_apply]
  have key : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * B k =
      ∑ i, (∑ j, X j * C (b.repr (x j * b k) i)) • B i := by
    simp only [hB, Algebra.smul_def, MvPolynomial.algebraMap_def, map_sum, map_mul,
      MvPolynomial.map_X, MvPolynomial.map_C, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← C_mul]
    conv_lhs => rw [← b.sum_repr (x j * b k)]
    simp only [map_sum, Finset.mul_sum, Algebra.smul_def, C_mul, mul_assoc]
  rw [key, B.repr_sum_self]
end GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange

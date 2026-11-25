-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_eq_det_ab85baa4cd14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:06.995371+00:00
-- url     : https://prove2.me/submissions/aafd5fb9-6f01-4a68-823c-1ca49fb77354

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_polyBasis_apply_c1352a7f2763

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
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (x : Fin n → A) :
    normForm A x = (∑ j, (X j : MvPolynomial (Fin n) R) • (Algebra.leftMulMatrix b (x j)).map C).det := by
  let bP := polyBasis b n
  let M : Fin n → Matrix ι ι R := fun j => Algebra.leftMulMatrix b (x j)
  have hM : ∀ j k, x j * b k = ∑ i, M j i k • b i := fun j k => by
    simp only [M, Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr (x j * b k)).symm
  have key : ∀ (q : MvPolynomial (Fin n) R) (a : A),
      q • (C a : MvPolynomial (Fin n) A) = MvPolynomial.map (algebraMap R A) q * C a := fun q a => by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_def]
  have hmat : Algebra.leftMulMatrix bP (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) =
      ∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C := by
    refine Matrix.ext fun i k => ?_
    rw [Algebra.leftMulMatrix_eq_repr_mul, polyBasis_apply]
    have hsum : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k) =
        ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
      calc (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k)
          = ∑ j, ∑ i', (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_assoc, ← C_mul, hM j k, map_sum, Finset.mul_sum]
        _ = ∑ i', ∑ j, (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := Finset.sum_comm
        _ = ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [polyBasis_apply, key, map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, map_X, map_C, Algebra.smul_def, C_mul, mul_assoc]
    rw [hsum, bP.repr_sum_self, Matrix.sum_apply]
    simp [Matrix.map_apply]
  rw [normForm, Algebra.norm_eq_matrix_det bP, hmat]
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible

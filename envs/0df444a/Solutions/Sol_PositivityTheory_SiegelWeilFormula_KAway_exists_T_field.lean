-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KAway.exists_T_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:22:49.0888+00:00
-- url     : https://prove2.me/submissions/d3a97358-4287-44b7-b7c6-e2a9896e98aa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem _root_.solution {K : Type} [Field K] [Infinite K] (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hX : X.det ≠ 0) :
    ∃ T : Matrix (Fin n) (Fin n) K, (X.toBlocks₁₁ - T * X.toBlocks₂₁).det ≠ 0 := by
  classical
  set A := X.toBlocks₁₁ with hA
  set C := X.toBlocks₂₁ with hC
  have hZX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hX)
  set P := (X⁻¹).toBlocks₁₁ with hP
  set Q := (X⁻¹).toBlocks₁₂ with hQ
  have hPQ : P * A + Q * C = 1 := by
    ext i j
    have h := congrFun (congrFun hZX (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hA, hC, hP, hQ, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using h
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (insert 0 ((-P).charpoly.roots.toFinset ∪ (-A).charpoly.roots.toFinset.image (·⁻¹)))
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  have hsP : (Matrix.scalar (Fin n) s - -P).det ≠ 0 := by
    intro h
    apply hs
    refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    exact (Matrix.eval_charpoly _ _).trans h
  have hsA : (Matrix.scalar (Fin n) s⁻¹ - -A).det ≠ 0 := by
    intro h
    apply hs
    refine Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨s⁻¹, ?_, inv_inv s⟩))
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    exact (Matrix.eval_charpoly _ _).trans h
  set U := Matrix.scalar (Fin n) s - -P with hU
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hsP
  refine ⟨-(U⁻¹ * Q), ?_⟩
  have hUA : U * A = s • A + P * A := by
    rw [hU, sub_neg_eq_add, Matrix.add_mul]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul]
  have key : U * (A - -(U⁻¹ * Q) * C) = s • (Matrix.scalar (Fin n) s⁻¹ - -A) := by
    rw [neg_mul, sub_neg_eq_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hUu, Matrix.one_mul, hUA, add_assoc, hPQ]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> field_simp <;> ring
  intro h0
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul] at this
  exact mul_ne_zero (pow_ne_zero _ hs0) hsA this.symm
end PositivityTheory.SiegelWeilFormula.KAway

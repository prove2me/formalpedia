-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.tensorCoordinateFormula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:06:24.938736+00:00
-- url     : https://prove2.me/submissions/975ed75b-1033-4a5b-b07d-fad778b7ed69

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false

noncomputable section
open scoped Matrix
open QAlgorithms.Papers.Independent.Independent1.P09
open QAlgorithms.ErrorMitigation

private lemma tensor_unit {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j))) : IsUnit (tensorFlat B) := by
  classical
  let C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℝ :=
    Matrix.of fun p i => ∏ j, (localFlat (B j))⁻¹ (p j) (i j)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨C, ?_⟩
  ext p q
  change (∑ i : Fin n → Fin 16, (∏ j, localFlat (B j) (p j) (i j)) *
    ∏ j, (localFlat (B j))⁻¹ (i j) (q j)) = (1 : Matrix _ _ ℝ) p q
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin n) (i : Fin 16) =>
    localFlat (B j) (p j) i * (localFlat (B j))⁻¹ i (q j))]
  have hlocal (j : Fin n) :
      (∑ i, localFlat (B j) (p j) i * (localFlat (B j))⁻¹ i (q j)) =
        (1 : Matrix (Fin 16) (Fin 16) ℝ) (p j) (q j) := by
    exact congrArg (fun A : Matrix (Fin 16) (Fin 16) ℝ => A (p j) (q j))
      (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (complete j)))
  simp_rw [hlocal]
  by_cases h : p = q
  · subst q
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne hj

private lemma interleave_injective {n : ℕ} :
    Function.Injective (interleave (n := n)) := by
  intro E F h
  ext a b
  let p : Fin n → Fin 16 := fun j => finProdFinEquiv (b j, a j)
  have he := congrFun h p
  simpa [interleave, p] using he

private lemma interleave_synthesis {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (q : (Fin n → Fin 16) → ℝ) :
    interleave (∑ i, q i • tensorOperation B i) = (tensorFlat B).mulVec q := by
  ext p
  simp only [interleave, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorOperation, tensorFlat, localFlat, localBasisMatrix, Matrix.of_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem solution {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    IsUnit (tensorFlat B) ∧
    E = ∑ i, tensorCoordinates B E i • tensorOperation B i ∧
    ∀ q, E = ∑ i, q i • tensorOperation B i → q = tensorCoordinates B E := by
  classical
  have hu := tensor_unit B complete
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  refine ⟨hu, ?_, ?_⟩
  · apply interleave_injective
    rw [interleave_synthesis]
    simp [tensorCoordinates, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd]
  · intro q hq
    have hv := congrArg interleave hq
    rw [interleave_synthesis] at hv
    unfold tensorCoordinates
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

#print axioms solution

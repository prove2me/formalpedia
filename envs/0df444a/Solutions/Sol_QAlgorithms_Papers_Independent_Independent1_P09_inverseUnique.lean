-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.inverseUnique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:02:42.616667+00:00
-- url     : https://prove2.me/submissions/789fc5e9-45bc-44d8-b5ee-e429ec3cc771

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P09
open ErrorMitigation

/-- PDF pp.5–6, §VIII: correction follows native map; both inverses guarded.
Coordinates use Eq. (2): printed D3 has its local row/column order reversed; swapping
those pairs preserves D1 and changes no inverse-method target. -/
theorem gk_interleave_op {n : ℕ} (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (q : (Fin n → Fin 16) → ℝ) :
    interleave (∑ i, q i • tensorOperation B i) = (tensorFlat B).mulVec q := by
  funext p
  simp only [interleave, Matrix.mulVec, dotProduct, tensorFlat, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, tensorOperation, localFlat, localBasisMatrix, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem gk_interleave_inj {n : ℕ} {E F : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ}
    (h : interleave E = interleave F) : E = F := by
  ext a b
  have := congrFun h (fun j => finProdFinEquiv (b j, a j))
  simpa [interleave] using this

theorem gk_tf_unit {n : ℕ} (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j))) : IsUnit (tensorFlat B) := by
  let M : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℝ :=
    Matrix.of fun i p => ∏ j, (localFlat (B j))⁻¹ (i j) (p j)
  have hinv : ∀ j, localFlat (B j) * (localFlat (B j))⁻¹ = 1 := fun j =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (complete j))
  have h : tensorFlat B * M = 1 := by
    ext p q
    simp only [Matrix.mul_apply, tensorFlat, M, Matrix.of_apply, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun j k => localFlat (B j) (p j) k * (localFlat (B j))⁻¹ k (q j))]
    simp only [← Matrix.mul_apply, hinv, Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq; simp
    · obtain ⟨j, hj⟩ : ∃ j, p j ≠ q j := by
        by_contra hc; push_neg at hc; exact hpq (funext hc)
      rw [if_neg hpq]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)

theorem gk_core {n : ℕ} (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j))) (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ)
    (q : (Fin n → Fin 16) → ℝ) :
    E = ∑ i, q i • tensorOperation B i ↔ q = tensorCoordinates B E := by
  have hu := gk_tf_unit B complete
  have hd : IsUnit (tensorFlat B).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  constructor
  · intro h
    rw [h, tensorCoordinates, gk_interleave_op, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd,
      Matrix.one_mulVec]
  · intro h
    apply gk_interleave_inj
    rw [gk_interleave_op, h, tensorCoordinates, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd,
      Matrix.one_mulVec]

theorem solution {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (ideal native : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ)
    (hi : IsUnit ideal) (hn : IsUnit native) :
    let noise := native*ideal⁻¹
    noise*ideal = native ∧ noise⁻¹ = ideal*native⁻¹ ∧
    ideal = (∑ i, tensorCoordinates B (ideal*native⁻¹) i • tensorOperation B i)*native ∧
    ∃! q : (Fin n → Fin 16) → ℝ, noise⁻¹ = ∑ i, q i • tensorOperation B i := by
  intro noise
  have hid : IsUnit ideal.det := (Matrix.isUnit_iff_isUnit_det _).mp hi
  have hnd : IsUnit native.det := (Matrix.isUnit_iff_isUnit_det _).mp hn
  have hinv : noise⁻¹ = ideal * native⁻¹ := by
    simp only [noise]
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hid]
  have hsum : ∑ i, tensorCoordinates B (ideal * native⁻¹) i • tensorOperation B i = ideal * native⁻¹ :=
    ((gk_core B complete (ideal * native⁻¹) _).mpr rfl).symm
  refine ⟨?_, hinv, ?_, ?_⟩
  · simp only [noise]; rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hid, Matrix.mul_one]
  · rw [hsum, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hnd, Matrix.mul_one]
  · rw [hinv]
    exact ⟨_, (gk_core B complete _ _).mpr rfl, fun q hq => (gk_core B complete _ q).mp hq⟩


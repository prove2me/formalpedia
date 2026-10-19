-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.qubit_gate_from_coherence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:11:11.17798+00:00
-- url     : https://prove2.me/submissions/7d3b0904-23af-4552-99a7-f05c7ee43f7a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.6, (B.1)–(B.4): two fixed branches implement U on every normalized input qubit. -/


theorem solution (U : Matrix.unitaryGroup Bool ℂ) :
    IsKrausFamily (qubitResourceKraus U) ∧
    (∀ b, PreservesDiagonalBranch (qubitResourceKraus U b)) ∧
    ∀ phi : EuclideanSpace ℂ Bool, IsState phi → ∀ b : Bool,
      act (qubitResourceKraus U b) (tensorVec phi (act hadamard (ket false))) =
        ((Real.sqrt 2)⁻¹ : ℂ) • tensorVec (act U phi) (ket b) := by
  have hU : star (U : Matrix Bool Bool ℂ) * U = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
  have e : ∀ i j, (star (U : Matrix Bool Bool ℂ) * U) i j = (1 : Matrix Bool Bool ℂ) i j := by
    rw [hU]; intros; rfl
  have e00 := e false false
  have e01 := e false true
  have e10 := e true false
  have e11 := e true true
  simp [Matrix.mul_apply, Fintype.sum_bool] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_⟩
  · unfold IsKrausFamily
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Fintype.sum_bool, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.conjTranspose_apply, qubitResourceKraus, Matrix.of_apply]
    cases a <;> cases b <;> cases c <;> cases d <;> simp <;> first
      | linear_combination e00 | linear_combination e01 | linear_combination e10
      | linear_combination e11 | skip
  · intro b X _ hX
    have hXd : X = Matrix.diagonal (fun i => X i i) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · rw [hX i j h]; simp [Matrix.diagonal_apply_ne _ h]
    rw [hXd]
    intro ⟨a1, a2⟩ ⟨c1, c2⟩ hne
    simp only [conjSuperop, Matrix.mul_diagonal, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_bool, Matrix.conjTranspose_apply, qubitResourceKraus, Matrix.of_apply]
    cases b <;> cases a1 <;> cases a2 <;> cases c1 <;> cases c2 <;> simp at hne ⊢
  · intro phi _ b
    ext ⟨a1, a2⟩
    simp only [act, tensorVec, ket, hadamard, qubitResourceKraus, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fintype.sum_bool, Matrix.of_apply, PiLp.smul_apply,
      EuclideanSpace.single_apply, smul_eq_mul]
    cases b <;> cases a1 <;> cases a2 <;> simp <;> ring


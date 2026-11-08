-- Prove2me | solution 1 for ObliviousRSP.card_smul_partialTraceLeft_maxEnt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:11:30.733614+00:00
-- url     : https://prove2.me/submissions/f05bc9f7-0d23-445f-a961-7bf1e54209d7

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_ObliviousRSP_maxEnt

open scoped Kronecker Matrix

open ObliviousRSP in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : Matrix ι ι ℂ) :
    (Fintype.card ι : ℂ) • WildeQIT.partialTraceLeft ((φᵀ ⊗ₖ (1 : Matrix ι ι ℂ)) * ObliviousRSP.maxEnt ι) =
      φ := by
  ext k l
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨k⟩
    exact_mod_cast this.ne'
  simp only [Matrix.smul_apply, WildeQIT.partialTraceLeft, Matrix.of_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.one_apply, ObliviousRSP.maxEnt,
    Fintype.sum_prod_type, smul_eq_mul]
  have e : ∀ i : ι, (∑ a : ι, ∑ b : ι, φ a i * (if k = b then 1 else 0) *
      (if a = b ∧ i = l then (Fintype.card ι : ℂ)⁻¹ else 0)) =
      if i = l then φ k i * (Fintype.card ι : ℂ)⁻¹ else 0 := by
    intro i
    by_cases hil : i = l
    · simp [hil]
    · simp [hil]
  rw [Finset.sum_congr rfl (fun i _ => e i)]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [mul_left_comm, mul_inv_cancel₀ hd, mul_one]

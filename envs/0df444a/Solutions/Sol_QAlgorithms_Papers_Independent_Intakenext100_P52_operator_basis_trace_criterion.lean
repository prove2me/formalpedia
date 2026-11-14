-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.operator_basis_trace_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T03:54:20.727208+00:00
-- url     : https://prove2.me/submissions/3e510796-3250-46df-9f67-f82a39083f85

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_rotatedEntangledKet_inner

open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Orthogonal operator bases, PDF p.4 Remark, corrected source typo:
printed Tr(U_i U_j†)=delta_ij; changed to d delta_ij because phi is normalized
and the ordinary unnormalized trace has Tr(I_d)=d. -/
theorem solution {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U : Fin (Fintype.card I ^ 2) → Matrix I I ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup I ℂ) :
    Orthonormal ℂ (fun i => rotatedEntangledKet (U i)) ↔
      ∀ i j, (U i * (U j)ᴴ).trace = if i = j then (Fintype.card I : ℂ) else 0 := by
  classical
  have hd : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [orthonormal_iff_ite]
  constructor
  · intro h i j
    have hij := h i j
    rw [rotatedEntangledKet_inner] at hij
    have hh := congrArg (fun z : ℂ => (Fintype.card I : ℂ) * z) hij
    by_cases he : i = j
    · simpa [he, ← mul_assoc, hd] using hh
    · simpa [he, ← mul_assoc, hd] using hh
  · intro h i j
    rw [rotatedEntangledKet_inner, h i j]
    split_ifs <;> simp [hd]
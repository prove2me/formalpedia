-- Prove2me | solution 1 for SiegelFields.reality_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:59:45.901218+00:00
-- url     : https://prove2.me/submissions/d10ef4d3-4ddc-4468-8a9d-f513107e6c73

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

set_option autoImplicit false

open Matrix Complex

lemma sfMatC_conj_2a6a79c6 (M : Matrix (Fin 2) (Fin 2) ℂ) :
    SiegelFields.matC * M * SiegelFields.matC = !![M 1 1, -M 1 0; -M 0 1, M 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SiegelFields.matC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    ring_nf <;> simp [I_sq]

open Matrix Complex SiegelFields in
theorem solution :
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V → V.map star = -(matC * V * matC)) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, U.map star = matC * U * matC) := by
  constructor
  · intro V hV
    have hV' : V 1 1 = -V 0 0 := by
      have h := hV.2
      simp [Matrix.trace, Fin.sum_univ_two] at h
      linear_combination h
    have hH := hV.1
    have h00 : (starRingEnd ℂ) (V 0 0) = V 0 0 := hH.apply 0 0
    have h11 : (starRingEnd ℂ) (V 1 1) = V 1 1 := hH.apply 1 1
    rw [sfMatC_conj_2a6a79c6]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
      rw [h00, hV']; ring
    · simp
      exact hH.apply 1 0
    · simp
      exact hH.apply 0 1
    · simp
      rw [h11, hV']
  · intro U hU
    rw [Matrix.mem_specialUnitaryGroup_iff] at hU
    obtain ⟨hU1, hdet⟩ := hU
    rw [Matrix.mem_unitaryGroup_iff'] at hU1
    have hadj : star U = U.adjugate := by
      have h2 : U * U.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
      calc star U = star U * (U * U.adjugate) := by rw [h2, mul_one]
        _ = (star U * U) * U.adjugate := by rw [Matrix.mul_assoc]
        _ = U.adjugate := by rw [hU1, Matrix.one_mul]
    have e : ∀ i j, star (U j i) = U.adjugate i j := by
      intro i j
      rw [← Matrix.star_apply, hadj]
    rw [Matrix.adjugate_fin_two] at e
    rw [sfMatC_conj_2a6a79c6]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using e 0 0
    · simpa using e 1 0
    · simpa using e 0 1
    · simpa using e 1 1

-- Prove2me | solution 1 for SiegelFields.unitary_conj_threeVector
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:47:04.700016+00:00
-- url     : https://prove2.me/submissions/13cbfdc6-1521-4b54-ad67-79bc3b0152d2

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex


namespace SiegelFields

lemma sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  exact_mod_cast this

lemma sqrt2_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast this

lemma vtm_eq (v : Fin 3 → ℝ) : vecToMatrix v =
    !![(Real.sqrt 2 : ℂ)⁻¹ * v 0, (Real.sqrt 2 : ℂ)⁻¹ * (v 1 - I * v 2);
       (Real.sqrt 2 : ℂ)⁻¹ * (v 1 + I * v 2), -((Real.sqrt 2 : ℂ)⁻¹ * v 0)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [vecToMatrix]

lemma vtm_isThreeVector (v : Fin 3 → ℝ) : IsThreeVector (vecToMatrix v) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vtm_eq, Matrix.conjTranspose_apply, Complex.ext_iff] <;> ring
  · simp [vtm_eq, Matrix.trace_fin_two]

lemma vtm_injective : Function.Injective vecToMatrix := by
  intro v w h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [vtm_eq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01
  have hs := sqrt2_ne
  have e0 : (v 0 : ℂ) = w 0 := by
    have := mul_left_cancel₀ (inv_ne_zero hs) h00; exact this
  have e1 : ((v 1 : ℂ) - I * v 2) = (w 1 - I * w 2) := mul_left_cancel₀ (inv_ne_zero hs) h01
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  simp at r1 i1
  funext i
  fin_cases i
  · exact_mod_cast e0
  · simpa using r1
  · simpa using i1

theorem m1 (V : Matrix (Fin 2) (Fin 2) ℂ) :
    IsThreeVector V ↔ ∃! v : Fin 3 → ℝ, V = vecToMatrix v := by
  constructor
  · rintro ⟨hH, hT⟩
    have h00 : star (V 0 0) = V 0 0 := by simpa using congrFun (congrFun hH 0) 0
    have h10 : star (V 0 1) = V 1 0 := by simpa using congrFun (congrFun hH 1) 0
    have h11 : V 1 1 = -V 0 0 := by
      rw [Matrix.trace_fin_two] at hT; linear_combination hT
    have him : (V 0 0).im = 0 := by
      have := congrArg Complex.im h00; simp at this; linarith
    refine ⟨![Real.sqrt 2 * (V 0 0).re, Real.sqrt 2 * (V 0 1).re,
      -(Real.sqrt 2 * (V 0 1).im)], ?_, fun w hw => vtm_injective ?_⟩
    · have hs : Real.sqrt 2 ≠ 0 := by positivity
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [vtm_eq, Complex.ext_iff, ← h10, h11, him] <;> field_simp <;>
          (try simp [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])
    · rw [← hw]
      have hs : Real.sqrt 2 ≠ 0 := by positivity
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [vtm_eq, Complex.ext_iff, ← h10, h11, him] <;> field_simp <;>
          (try simp [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])
  · rintro ⟨v, rfl, -⟩
    exact vtm_isThreeVector v

theorem m2 (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : IsThreeVector V) :
    IsThreeVector (U * V * Uᴴ) ∧ (U * V * Uᴴ).det = V.det := by
  have hUU : Uᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hU; simpa [Matrix.star_eq_conjTranspose] using this
  have hUU' : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU; simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hV.1.eq, Matrix.mul_assoc]
  · rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, hV.2]
  · rw [Matrix.det_mul, Matrix.det_mul, mul_comm (U.det), mul_assoc, ← Matrix.det_mul, hUU',
      Matrix.det_one, mul_one]


lemma unitary_left {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Uᴴ * U = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hU; simpa [Matrix.star_eq_conjTranspose] using this

lemma unitary_right {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U * Uᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp hU; simpa [Matrix.star_eq_conjTranspose] using this

lemma vtm_lin (v : Fin 3 → ℝ) : vecToMatrix v = ∑ j, (v j : ℂ) • basisMatrix j := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [basisMatrix, vtm_eq, Fin.sum_univ_three, Pi.single_apply] <;> ring

lemma coord (i : Fin 3) (v : Fin 3 → ℝ) : (trace (basisMatrix i * vecToMatrix v)).re = v i := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  fin_cases i
  · simp [basisMatrix, vtm_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_two,
      Pi.single_apply]; field_simp; linear_combination 2 * (v 0) * h2
  · simp [basisMatrix, vtm_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_two,
      Pi.single_apply]; field_simp; linear_combination 2 * (v 1) * h2
  · simp [basisMatrix, vtm_eq, Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_two,
      Pi.single_apply]; field_simp; linear_combination 2 * (v 2) * h2

theorem m4 (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (v : Fin 3 → ℝ) :
    U * vecToMatrix v * Uᴴ = vecToMatrix (rotationOf U *ᵥ v) := by
  obtain ⟨w, hw, -⟩ := (m1 _).mp (m2 U hU _ (vtm_isThreeVector v)).1
  rw [hw]
  congr 1
  funext i
  have hc := coord i w
  rw [← hw] at hc
  rw [← hc]
  simp only [Matrix.mulVec, dotProduct, rotationOf, Matrix.of_apply]
  rw [vtm_lin v]
  have hterm : ∀ j, basisMatrix i * (U * ((v j : ℂ) • basisMatrix j) * Uᴴ) =
      (v j : ℂ) • (basisMatrix i * U * basisMatrix j * Uᴴ) := by
    intro j
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum]
  simp only [hterm, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, smul_eq_mul,
    Complex.re_ofReal_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem m3 (U W : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V → U * V * Uᴴ = W * V * Wᴴ) ↔
      W = U ∨ W = -U := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hU hW
  have hUU := unitary_left hU.1
  have hWW := unitary_left hW.1
  have hWW' := unitary_right hW.1
  constructor
  · intro h
    set X := Wᴴ * U with hX
    have hcomm : ∀ V, IsThreeVector V → X * V = V * X := by
      intro V hV
      have e1 : Wᴴ * (U * V * Uᴴ) * U = X * V := by
        rw [hX]; simp only [Matrix.mul_assoc, hUU, Matrix.mul_one]
      have e2 : Wᴴ * (W * V * Wᴴ) * U = V * X := by
        rw [hX]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Wᴴ W, hWW, Matrix.one_mul]
      rw [← e1, ← e2, h V hV]
    have hs : ((Real.sqrt 2 : ℂ))⁻¹ ≠ 0 := inv_ne_zero sqrt2_ne
    have c0 := hcomm _ (vtm_isThreeVector (Pi.single 0 1))
    have c1 := hcomm _ (vtm_isThreeVector (Pi.single 1 1))
    have q01 := congrFun (congrFun c0 0) 1
    have q10 := congrFun (congrFun c0 1) 0
    have q01' := congrFun (congrFun c1 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, vtm_eq, Pi.single_apply] at q01 q10 q01'
    have x01 : X 0 1 = 0 := by
      have : (2 * (Real.sqrt 2 : ℂ)⁻¹) * X 0 1 = 0 := by linear_combination -q01
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (mul_ne_zero two_ne_zero hs)
      · exact h0
    have x10 : X 1 0 = 0 := by
      have : (2 * (Real.sqrt 2 : ℂ)⁻¹) * X 1 0 = 0 := by linear_combination q10
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (mul_ne_zero two_ne_zero hs)
      · exact h0
    have x11 : X 1 1 = X 0 0 := by
      have : (Real.sqrt 2 : ℂ)⁻¹ * (X 1 1 - X 0 0) = 0 := by linear_combination -q01'
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hs
      · linear_combination h0
    have hXc : X = X 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext a b; fin_cases a <;> fin_cases b <;> simp [x01, x10, x11]
    have hdet : X.det = 1 := by
      rw [hX, Matrix.det_mul, Matrix.det_conjTranspose, hW.2, hU.2]; simp
    have hsq : X 0 0 * X 0 0 = 1 := by
      rw [Matrix.det_fin_two, x01, x10, x11] at hdet; linear_combination hdet
    have hUX : U = X 0 0 • W := by
      calc U = W * X := by rw [hX, ← Matrix.mul_assoc, hWW', Matrix.one_mul]
        _ = X 0 0 • W := by conv_lhs => rw [hXc]
                            rw [Matrix.mul_smul, Matrix.mul_one]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left; rw [hUX, h1, one_smul]
    · right; rw [hUX, h1, neg_one_smul, neg_neg]
  · rintro (rfl | rfl) V _
    · rfl
    · simp [Matrix.conjTranspose_neg]

end SiegelFields

open SiegelFields

theorem solution (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : IsThreeVector V) :
    IsThreeVector (U * V * Uᴴ) ∧ (U * V * Uᴴ).det = V.det := by
  exact m2 U hU V hV

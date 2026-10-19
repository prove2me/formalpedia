-- Prove2me | solution 1 for QAlgorithms.Nannicini.quantumSearch_unknownCount_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:57:40.097521+00:00
-- url     : https://prove2.me/submissions/919422c0-a947-4752-a1bf-6c27472daf72

import Theorems.Thm_QAlgorithms_Nannicini_quantumSearch_unknownCount
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false

open QAlgorithms QAlgorithms.Nannicini
open scoped ENNReal

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Qubits n → Bool),
      1 ≤ (Finset.univ.filter fun j => f j = true).card →
        (∑' oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc) = 1 ∧
        (∀ oc : Option (Qubits n) × ℕ, searchAlg1Weight f oc ≠ 0 →
          ∃ j, oc.1 = some j ∧ f j = true) ∧
        searchAlg1ExpectedCost f ≤
          ENNReal.ofReal (C * Real.sqrt ((2 : ℝ) ^ n /
            ((Finset.univ.filter fun j => f j = true).card : ℝ))) := by
  classical
  obtain ⟨C, hC, hsearch⟩ := quantumSearch_unknownCount
  refine ⟨C, hC, ?_⟩
  intro n f hM
  let t := (Finset.univ.filter fun j => f j = true).card
  have ht : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t from hM)
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have htN : (t : ℝ) ≤ (2 : ℝ) ^ n := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Qubits n)) (fun j => f j = true)
    simpa [t, Qubits] using (show (t : ℝ) ≤ (Fintype.card (Qubits n) : ℝ) by exact_mod_cast h)
  have hp : 0 < (t : ℝ) / (2 : ℝ) ^ n := div_pos ht hN
  have hp1 : (t : ℝ) / (2 : ℝ) ^ n ≤ 1 := (div_le_one hN).2 htN
  have hspos : 0 < Real.sqrt ((t : ℝ) / (2 : ℝ) ^ n) := Real.sqrt_pos.2 hp
  have hs1 : Real.sqrt ((t : ℝ) / (2 : ℝ) ^ n) ≤ 1 := (Real.sqrt_le_one).2 hp1
  have hangle : 0 < groverAngle t (2 ^ n) := by
    simpa [groverAngle] using Real.arcsin_pos.2 hspos
  have hbound : Real.sqrt ((t : ℝ) / (2 : ℝ) ^ n) ≤ groverAngle t (2 ^ n) := by
    have h := Real.sin_le (Real.arcsin_nonneg.2 hspos.le)
    rw [Real.sin_arcsin (by linarith : -1 ≤ Real.sqrt ((t : ℝ) / (2 : ℝ) ^ n)) hs1] at h
    simpa only [groverAngle, Nat.cast_pow, Nat.cast_ofNat] using h
  have hinv : 1 / Real.sqrt ((t : ℝ) / (2 : ℝ) ^ n) =
      Real.sqrt ((2 : ℝ) ^ n / (t : ℝ)) := by
    rw [one_div, ← Real.sqrt_inv, inv_div]
  obtain ⟨hmass, hout, hcost⟩ := (hsearch n f).1 hangle
  refine ⟨hmass, hout, hcost.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  calc
    C / groverAngle t (2 ^ n) ≤ C / Real.sqrt ((t : ℝ) / (2 : ℝ) ^ n) :=
      div_le_div_of_nonneg_left hC.le hspos hbound
    _ = C * Real.sqrt ((2 : ℝ) ^ n / (t : ℝ)) := by rw [div_eq_mul_one_div, hinv]

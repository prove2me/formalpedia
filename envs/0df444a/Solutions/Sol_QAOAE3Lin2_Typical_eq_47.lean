-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T13:10:02.538214+00:00
-- url     : https://prove2.me/submissions/c8e9ffc5-9fc4-48ea-ac77-bb74c7a95641

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting
import Theorems.Thm_QAOAE3Lin2_Typical_eq_25

open QAlgorithms QAOAE3Lin2.Typical

/-- The trigonometric identity behind (47): the four sign patterns of (25) at `d = 1`, minus the
same at `d = -1`, give `8 sin γ cos(γ c₁) cos(γ c₂) cos(γ c₃)`. -/
theorem e47_trig (γ c₁ c₂ c₃ : ℝ) :
    (Real.sin (γ * (1 + c₁ + c₂ + c₃)) + Real.sin (γ * (1 + c₁ - c₂ - c₃)) +
        Real.sin (γ * (1 - c₁ + c₂ - c₃)) + Real.sin (γ * (1 - c₁ - c₂ + c₃))) -
      (Real.sin (γ * (-1 + c₁ + c₂ + c₃)) + Real.sin (γ * (-1 + c₁ - c₂ - c₃)) +
        Real.sin (γ * (-1 - c₁ + c₂ - c₃)) + Real.sin (γ * (-1 - c₁ - c₂ + c₃))) =
      8 * Real.sin γ * (Real.cos (γ * c₁) * Real.cos (γ * c₂) * Real.cos (γ * c₃)) := by
  rw [show γ * (1 + c₁ + c₂ + c₃) = γ + γ * c₁ + γ * c₂ + γ * c₃ by ring,
    show γ * (1 + c₁ - c₂ - c₃) = γ + γ * c₁ - γ * c₂ - γ * c₃ by ring,
    show γ * (1 - c₁ + c₂ - c₃) = γ + γ * c₂ - γ * c₁ - γ * c₃ by ring,
    show γ * (1 - c₁ - c₂ + c₃) = γ + γ * c₃ - γ * c₁ - γ * c₂ by ring,
    show γ * (-1 + c₁ + c₂ + c₃) = γ * c₁ + γ * c₂ + γ * c₃ - γ by ring,
    show γ * (-1 + c₁ - c₂ - c₃) = γ * c₁ - γ - γ * c₂ - γ * c₃ by ring,
    show γ * (-1 - c₁ + c₂ - c₃) = γ * c₂ - γ - γ * c₁ - γ * c₃ by ring,
    show γ * (-1 - c₁ - c₂ + c₃) = γ * c₃ - γ - γ * c₁ - γ * c₂ by ring]
  simp only [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
  ring

/-- The polynomials `c_r` of equation `i` do not involve the sign of equation `i` itself. -/
theorem e47_cPoly_update {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (i : Fin m) (b : Bool) (r : Fin 3) (x : Qubits n) :
    QAOAE3Lin2.General.cPoly tri (Function.update rhs i b) i r x =
      QAOAE3Lin2.General.cPoly tri rhs i r x := by
  unfold QAOAE3Lin2.General.cPoly
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : QAOAE3Lin2.General.sharesOnly tri i j r
  · rw [if_pos h, if_pos h]
    have hji : j ≠ i := h.1
    have hs : QAOAE3Lin2.General.sgn (Function.update rhs i b) j = QAOAE3Lin2.General.sgn rhs j := by
      unfold QAOAE3Lin2.General.sgn
      rw [Function.update_of_ne hji]
    rw [hs]
  · rw [if_neg h, if_neg h]

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) :
    (clauseTerm tri (Function.update rhs i false) i γ +
        clauseTerm tri (Function.update rhs i true) i γ) / 2 =
      (1 / 2) * Real.sin γ * QAOAE3Lin2.General.avgZ (fun x => Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i 0 x) *
        Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i 1 x) * Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i 2 x)) := by
  have hs0 : QAOAE3Lin2.General.sgn (Function.update rhs i false) i = 1 := by
    simp [QAOAE3Lin2.General.sgn]
  have hs1 : QAOAE3Lin2.General.sgn (Function.update rhs i true) i = -1 := by
    simp [QAOAE3Lin2.General.sgn]
  -- the two instances of (25), with the signs evaluated and the `c`'s freed from the update
  have h0 : clauseTerm tri (Function.update rhs i false) i γ =
      (1 / 8) * QAOAE3Lin2.General.avgZ (fun x =>
        Real.sin (γ * (1 + QAOAE3Lin2.General.cPoly tri rhs i 0 x + QAOAE3Lin2.General.cPoly tri rhs i 1 x +
            QAOAE3Lin2.General.cPoly tri rhs i 2 x)) +
          Real.sin (γ * (1 + QAOAE3Lin2.General.cPoly tri rhs i 0 x - QAOAE3Lin2.General.cPoly tri rhs i 1 x -
            QAOAE3Lin2.General.cPoly tri rhs i 2 x)) +
          Real.sin (γ * (1 - QAOAE3Lin2.General.cPoly tri rhs i 0 x + QAOAE3Lin2.General.cPoly tri rhs i 1 x -
            QAOAE3Lin2.General.cPoly tri rhs i 2 x)) +
          Real.sin (γ * (1 - QAOAE3Lin2.General.cPoly tri rhs i 0 x - QAOAE3Lin2.General.cPoly tri rhs i 1 x +
            QAOAE3Lin2.General.cPoly tri rhs i 2 x))) := by
    rw [eq_25 tri htri (Function.update rhs i false) i γ]
    unfold QAOAE3Lin2.General.clauseSin
    simp only [hs0, e47_cPoly_update, mul_one]
  have h1 : clauseTerm tri (Function.update rhs i true) i γ =
      -((1 / 8) * QAOAE3Lin2.General.avgZ (fun x =>
        Real.sin (γ * (-1 + QAOAE3Lin2.General.cPoly tri rhs i 0 x + QAOAE3Lin2.General.cPoly tri rhs i 1 x +
            QAOAE3Lin2.General.cPoly tri rhs i 2 x)) +
          Real.sin (γ * (-1 + QAOAE3Lin2.General.cPoly tri rhs i 0 x - QAOAE3Lin2.General.cPoly tri rhs i 1 x -
            QAOAE3Lin2.General.cPoly tri rhs i 2 x)) +
          Real.sin (γ * (-1 - QAOAE3Lin2.General.cPoly tri rhs i 0 x + QAOAE3Lin2.General.cPoly tri rhs i 1 x -
            QAOAE3Lin2.General.cPoly tri rhs i 2 x)) +
          Real.sin (γ * (-1 - QAOAE3Lin2.General.cPoly tri rhs i 0 x - QAOAE3Lin2.General.cPoly tri rhs i 1 x +
            QAOAE3Lin2.General.cPoly tri rhs i 2 x)))) := by
    rw [eq_25 tri htri (Function.update rhs i true) i γ]
    unfold QAOAE3Lin2.General.clauseSin
    simp only [hs1, e47_cPoly_update, mul_neg, mul_one, neg_mul]
  rw [h0, h1]
  unfold QAOAE3Lin2.General.avgZ
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Qubits n))) rfl
    (fun x _ => e47_trig γ (QAOAE3Lin2.General.cPoly tri rhs i 0 x)
      (QAOAE3Lin2.General.cPoly tri rhs i 1 x) (QAOAE3Lin2.General.cPoly tri rhs i 2 x))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linear_combination ((Fintype.card (Qubits n) : ℝ)⁻¹ / 16) * hsum

-- Prove2me | solution 1 for ShiShallow.majority_weight_eq_conj_majority_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T04:52:31.672615+00:00
-- url     : https://prove2.me/submissions/81cc44be-1b52-46d4-bee4-49d133d06bca

/-
TCON-2A (assembly, step 1 of the spectral soundness bound): the COUNT-FORM MAJORITY WEIGHT of
`Matrix.mulVec V Φ` is the quadratic form of the conjugated inclusion-exclusion operator at `Φ`.

This is the operator-identity half of the threefold-majority soundness bound: it converts a
weight (a sum of squared amplitudes over the accepting basis strings) into a quadratic form in
the three CONJUGATED single-wire projectors `star V * projOut w * V`, which is the shape the
spectral half consumes.  Nothing here is specific to three copies of a circuit: `V` is any
isometry and `w1 w2 w3` are any three wires.

Cited platform theorems (both Proved):
* `ShiShallow.projOut_majority_inclusion_exclusion`
* `ShiShallow.conj_majority_inclusion_exclusion_of_unitary`

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiShallow_projOut_majority_inclusion_exclusion
import Theorems.Thm_ShiShallow_conj_majority_inclusion_exclusion_of_unitary

set_option autoImplicit false

open ShiShallow

/-- `Matrix.mulVec` as an explicit sum (definitional). -/
private lemma shiSnd_mulVec_sum {N : ℕ} (A : Op N) (v : Bits N → ℂ) (y : Bits N) :
    Matrix.mulVec A v y = ∑ z : Bits N, A y z * v z := by
  first
    | rfl
    | (simp only [Matrix.mulVec, dotProduct]; done)
    | (simp [Matrix.mulVec, dotProduct]; done)

/-- `conj z * z` is the real number `‖z‖ ^ 2`. -/
private lemma shiSnd_conj_mul_self (z : ℂ) :
    (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- Moving `star V` from the second slot of the sesquilinear form to the first. -/
private lemma shiSnd_move_star {N : ℕ} (V : Op N) (u Φ : Bits N → ℂ) :
    (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec (star V) u y)
      = ∑ y : Bits N, (starRingEnd ℂ) (Matrix.mulVec V Φ y) * u y := by
  simp only [shiSnd_mulVec_sum, Matrix.star_apply, map_sum, map_mul, starRingEnd_apply,
    star_star, Finset.mul_sum, Finset.sum_mul]
  first
    | (rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
       ring)
    | (refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
       ring)

/-- **Majority weight = conjugated inclusion-exclusion quadratic form.**

For an isometry `V` (`star V * V = 1`) and three wires `w1 w2 w3`, the weight that
`Matrix.mulVec V Φ` puts on the basis strings where at least two of the three wires read `1`
equals the real part of the quadratic form, at `Φ`, of the inclusion-exclusion polynomial in
the three conjugated projectors `star V * projOut wj * V`. -/
theorem solution {N : ℕ} (V : Op N) (hV : star V * V = (1 : Op N))
    (w1 w2 w3 : Fin N) (Φ : Bits N → ℂ) :
    (∑ y : Bits N,
        if 2 ≤ (if y w1 = true then (1 : ℕ) else 0) + (if y w2 = true then (1 : ℕ) else 0)
              + (if y w3 = true then (1 : ℕ) else 0)
          then ‖Matrix.mulVec V Φ y‖ ^ 2 else 0)
      = (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec
            ((star V * projOut w1 * V) * (star V * projOut w2 * V)
              + (star V * projOut w2 * V) * (star V * projOut w3 * V)
              + (star V * projOut w3 * V) * (star V * projOut w1 * V)
              - 2 * ((star V * projOut w1 * V) * (star V * projOut w2 * V)
                  * (star V * projOut w3 * V))) Φ y).re := by
  classical
  -- the count-form majority projector, named once
  obtain ⟨Pi, hPi⟩ : ∃ X : Op N, X = Matrix.of (fun a b : Bits N =>
      if a = b ∧ 2 ≤ (if a w1 = true then (1 : ℕ) else 0)
            + (if a w2 = true then (1 : ℕ) else 0) + (if a w3 = true then (1 : ℕ) else 0)
        then (1 : ℂ) else 0) := ⟨_, rfl⟩
  -- it is diagonal, so it acts as the indicator of the accepting strings
  have hdiag : ∀ (φ : Bits N → ℂ) (y : Bits N), Matrix.mulVec Pi φ y
      = if 2 ≤ (if y w1 = true then (1 : ℕ) else 0) + (if y w2 = true then (1 : ℕ) else 0)
            + (if y w3 = true then (1 : ℕ) else 0) then φ y else 0 := by
    intro φ y
    rw [hPi, shiSnd_mulVec_sum]
    by_cases h : 2 ≤ (if y w1 = true then (1 : ℕ) else 0)
        + (if y w2 = true then (1 : ℕ) else 0) + (if y w3 = true then (1 : ℕ) else 0)
    · rw [if_pos h,
        Finset.sum_eq_single_of_mem y (Finset.mem_univ y) (fun z _ hz => by
          have hyz : ¬ (y = z) := fun e => hz e.symm
          simp [Matrix.of_apply, hyz])]
      simp [Matrix.of_apply, h]
    · rw [if_neg h]
      refine Finset.sum_eq_zero ?_
      intro z _
      simp [Matrix.of_apply, h]
  -- the weight is the quadratic form of the conjugated projector
  have hquad : (∑ y : Bits N, (starRingEnd ℂ) (Φ y)
        * Matrix.mulVec (star V * Pi * V) Φ y)
      = ((∑ y : Bits N,
            if 2 ≤ (if y w1 = true then (1 : ℕ) else 0)
                  + (if y w2 = true then (1 : ℕ) else 0)
                  + (if y w3 = true then (1 : ℕ) else 0)
              then ‖Matrix.mulVec V Φ y‖ ^ 2 else 0 : ℝ) : ℂ) := by
    have h1 : Matrix.mulVec (star V * Pi * V) Φ
        = Matrix.mulVec (star V) (Matrix.mulVec Pi (Matrix.mulVec V Φ)) := by
      first
        | (simp only [← Matrix.mulVec_mulVec]; done)
        | (rw [mul_assoc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; done)
        | (simp only [Matrix.mulVec_mulVec, mul_assoc]; done)
    rw [h1, shiSnd_move_star]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hdiag]
    by_cases hy : 2 ≤ (if y w1 = true then (1 : ℕ) else 0)
        + (if y w2 = true then (1 : ℕ) else 0) + (if y w3 = true then (1 : ℕ) else 0)
    · rw [if_pos hy, if_pos hy]
      exact shiSnd_conj_mul_self _
    · rw [if_neg hy, if_neg hy, mul_zero, Complex.ofReal_zero]
  -- rewrite the conjugated inclusion-exclusion polynomial back into `star V * Pi * V`
  rw [← conj_majority_inclusion_exclusion_of_unitary V (projOut w1) (projOut w2) (projOut w3) hV,
    ← projOut_majority_inclusion_exclusion w1 w2 w3, ← hPi, hquad, Complex.ofReal_re]

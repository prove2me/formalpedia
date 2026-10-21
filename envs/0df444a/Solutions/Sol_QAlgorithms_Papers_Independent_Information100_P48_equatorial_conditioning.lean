-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.equatorial_conditioning
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T09:00:53.18104+00:00
-- url     : https://prove2.me/submissions/490e7eb8-a063-4d4f-b995-ac6eceb21e4a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P48

namespace G56EQ

lemma cos_pa (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Real.cos (principalAngle g) = Real.sqrt (1 - g) := by
  unfold principalAngle
  rw [Real.cos_arcsin, Real.sq_sqrt hg0]

lemma sin_pa (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Real.sin (principalAngle g) = Real.sqrt g := by
  unfold principalAngle
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg g]) (Real.sqrt_le_one.mpr hg1)]

set_option maxHeartbeats 4000000 in
lemma tr_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : QOp) :
    (independentADC g false ρ).trace = ρ false false + (1 - (g : ℂ) / 2) * ρ true true := by
  have h1 : (Real.sqrt (1 - g) : ℂ) ^ 2 = 1 - (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  have h2 : (Real.sqrt g : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  simp [Matrix.trace, independentADC, branch, cross, selectedOperator, outcomeSign,
      traceEnv, cleanInput, embed0, embed1, dilation, adcUnitary, cos_pa g hg0 hg1, sin_pa g hg0 hg1,
      Matrix.mul_apply, pairMatrix, pairIndex, Fintype.sum_prod_type, Matrix.kronecker, Matrix.single_apply]
  ring_nf
  simp [h1, h2]
  ring

lemma tr_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ρ : QOp) :
    (sharedADC g false ρ).trace = ρ false false + (1 - (g : ℂ)) * ρ true true := by
  have h1 : (Real.sqrt (1 - g) : ℂ) ^ 2 = 1 - (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  have h2 : (Real.sqrt g : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  simp [Matrix.trace, sharedADC, branch, cross, selectedOperator, outcomeSign,
      traceEnv, cleanInput, dilation, adcUnitary, cos_pa g hg0 hg1, sin_pa g hg0 hg1,
      Matrix.mul_apply, pairMatrix, pairIndex, Fintype.sum_prod_type, Matrix.kronecker, Matrix.single_apply]
  ring_nf
  simp [h1, h2]
  ring

lemma proj_ff (a : Fin 3 → ℝ) (m : Bool) :
    projector (bloch a) m false false = ((1 + outcomeSign m * a 2) / 2 : ℝ) := by
  simp [projector, bloch, pauli, Fin.sum_univ_three, pauliX, pauliY, pauliZ]
  push_cast; ring

lemma proj_tt (a : Fin 3 → ℝ) (m : Bool) :
    projector (bloch a) m true true = ((1 - outcomeSign m * a 2) / 2 : ℝ) := by
  simp [projector, bloch, pauli, Fin.sum_univ_three, pauliX, pauliY, pauliZ]
  push_cast; ring

lemma bs_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (a : Fin 3 → ℝ) (m : Bool) :
    branchSuccess (independentADC g false) a m = 1 - g / 4 + outcomeSign m * g / 4 * a 2 := by
  unfold branchSuccess
  rw [tr_ind g hg0 hg1, proj_ff, proj_tt]
  have : ((1 + outcomeSign m * a 2) / 2 : ℝ) + (1 - g / 2) * ((1 - outcomeSign m * a 2) / 2) =
      1 - g / 4 + outcomeSign m * g / 4 * a 2 := by ring
  rw [← this]
  simp

lemma bs_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (a : Fin 3 → ℝ) (m : Bool) :
    branchSuccess (sharedADC g false) a m = 1 - g / 2 + outcomeSign m * g / 2 * a 2 := by
  unfold branchSuccess
  rw [tr_sh g hg0 hg1, proj_ff, proj_tt]
  have : ((1 + outcomeSign m * a 2) / 2 : ℝ) + (1 - g) * ((1 - outcomeSign m * a 2) / 2) =
      1 - g / 2 + outcomeSign m * g / 2 * a 2 := by ring
  rw [← this]
  simp

lemma succ_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : success (independentADC g false) = 1 - g / 4 := by
  unfold success
  rw [tr_ind g hg0 hg1]
  simp [mixedQubit]; ring

lemma succ_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : success (sharedADC g false) = 1 - g / 2 := by
  unfold success
  rw [tr_sh g hg0 hg1]
  simp [mixedQubit]; ring

end G56EQ

open G56EQ in
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (∀ a : Fin 3 → ℝ, UnitDirection a → ∀ minus : Bool,
      branchSuccess (independentADC g false) a minus =
        1 - g / 4 + outcomeSign minus * g / 4 * a 2 ∧
      branchSuccess (sharedADC g false) a minus =
        1 - g / 2 + outcomeSign minus * g / 2 * a 2) ∧
    (∀ a : Fin 3 → ℝ, UnitDirection a → a 2 = 0 → ∀ minus : Bool,
      branchSuccess (independentADC g false) a minus = 1 - g / 4 ∧
      branchSuccess (sharedADC g false) a minus = 1 - g / 2) ∧
    (∀ a : Fin 3 → ℝ, UnitDirection a →
      (branchSuccess (independentADC g false) a false +
        branchSuccess (independentADC g false) a true) / 2 =
          success (independentADC g false) ∧
      (branchSuccess (sharedADC g false) a false +
        branchSuccess (sharedADC g false) a true) / 2 = success (sharedADC g false)) ∧
    ((branchSuccess (independentADC g false) ![0, 0, 1] false =
      branchSuccess (independentADC g false) ![0, 0, 1] true) ↔ g = 0) ∧
    ((branchSuccess (sharedADC g false) ![0, 0, 1] false =
      branchSuccess (sharedADC g false) ![0, 0, 1] true) ↔ g = 0) := by
  refine ⟨fun a _ m => ⟨bs_ind g hg0 hg1 a m, bs_sh g hg0 hg1 a m⟩, fun a _ h0 m => ?_,
    fun a _ => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [bs_ind g hg0 hg1, bs_sh g hg0 hg1, h0]; constructor <;> ring
  · rw [bs_ind g hg0 hg1, bs_ind g hg0 hg1, succ_ind g hg0 hg1]; simp [outcomeSign]; ring
  · rw [bs_sh g hg0 hg1, bs_sh g hg0 hg1, succ_sh g hg0 hg1]; simp [outcomeSign]; ring
  · rw [bs_ind g hg0 hg1, bs_ind g hg0 hg1]; simp [outcomeSign]; constructor <;> intro h <;> linarith
  · rw [bs_sh g hg0 hg1, bs_sh g hg0 hg1]; simp [outcomeSign]; constructor <;> intro h <;> linarith

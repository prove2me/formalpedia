-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.amplitudeDampingComposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:13:30.567735+00:00
-- url     : https://prove2.me/submissions/22d8895e-0760-45b6-820a-7a9b37f3e819

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace X5AD
open QAlgorithms.Papers.Independent.Gap20.P19

lemma ad_apply (u : ℝ) (ρ : Matrix Bool Bool ℂ) :
    rankTwoQubitMap u u ρ false false =
        ρ false false + ((Real.sin u ^ 2 : ℝ) : ℂ) * ρ true true ∧
    rankTwoQubitMap u u ρ false true = (Real.cos u : ℂ) * ρ false true ∧
    rankTwoQubitMap u u ρ true false = (Real.cos u : ℂ) * ρ true false ∧
    rankTwoQubitMap u u ρ true true = ((Real.cos u ^ 2 : ℝ) : ℂ) * ρ true true := by
  have h1 : (u + u) / 2 = u := by ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [rankTwoQubitMap, QAlgorithms.krausApply, canonicalKraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply, h1, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal] <;>
  ring

end X5AD


open QAlgorithms.Papers.Independent.Gap20.P19 in
theorem solution (u1 u2 : ℝ) :
    rankTwoQubitMap u1 u1 ∘ rankTwoQubitMap u2 u2 =
      rankTwoQubitMap (Real.arccos (Real.cos u1*Real.cos u2))
        (Real.arccos (Real.cos u1*Real.cos u2)) := by
  set w := Real.arccos (Real.cos u1 * Real.cos u2) with hw
  have hb : -1 ≤ Real.cos u1 * Real.cos u2 ∧ Real.cos u1 * Real.cos u2 ≤ 1 := by
    have a1 := Real.abs_cos_le_one u1
    have a2 := Real.abs_cos_le_one u2
    have : |Real.cos u1 * Real.cos u2| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg (Real.cos u1), abs_nonneg (Real.cos u2)]
    exact abs_le.1 this
  have hc : Real.cos w = Real.cos u1 * Real.cos u2 := Real.cos_arccos hb.1 hb.2
  have hs : Real.sin w ^ 2 = 1 - (Real.cos u1 * Real.cos u2) ^ 2 := by
    rw [← hc]; linarith [Real.sin_sq_add_cos_sq w]
  have s1 : Real.sin u1 ^ 2 = 1 - Real.cos u1 ^ 2 := by linarith [Real.sin_sq_add_cos_sq u1]
  have s2 : Real.sin u2 ^ 2 = 1 - Real.cos u2 ^ 2 := by linarith [Real.sin_sq_add_cos_sq u2]
  funext ρ
  ext i j
  obtain ⟨a1, a2, a3, a4⟩ := X5AD.ad_apply u1 (rankTwoQubitMap u2 u2 ρ)
  obtain ⟨b1, b2, b3, b4⟩ := X5AD.ad_apply u2 ρ
  obtain ⟨c1, c2, c3, c4⟩ := X5AD.ad_apply w ρ
  simp only [Function.comp]
  cases i <;> cases j
  · rw [a1, b1, b4, c1, hs, s1, s2]; push_cast; ring
  · rw [a2, b2, c2, hc]; push_cast; ring
  · rw [a3, b3, c3, hc]; push_cast; ring
  · rw [a4, b4, c4, hc]; push_cast; ring

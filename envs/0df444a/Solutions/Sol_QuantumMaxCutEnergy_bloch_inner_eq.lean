-- Prove2me | solution 1 for QuantumMaxCutEnergy.bloch_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:28:12.353105+00:00
-- url     : https://prove2.me/submissions/ae8f6c1c-e565-4653-b494-3bbcd1dc8c29

import Mathlib
import Definitions.Def_QuantumMaxCutEnergy_bloch

/-!
# The Bloch parametrisation and the two-qubit correlation identity

A qubit amplitude pair `(α, β) : ℂ × ℂ` with `|α|² + |β|² = 1` defines the Bloch vector

  `bloch α β = (2 Re (conj α * β), 2 Im (conj α * β), |α|² − |β|²)`.

The identity proved here is the one that links a product state to the classical relaxation
objective: for two normalised pairs,

  `2 |βa * αb − αa * βb|² = 1 − ⟪bloch αa βa, bloch αb βb⟫`.

It is algebraic — no trigonometry — which is what makes it usable for the rounding argument.
-/

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

@[simp] theorem bloch_zero (α β : ℂ) : bloch α β 0 = 2 * (α.re * β.re + α.im * β.im) := rfl
@[simp] theorem bloch_one (α β : ℂ) : bloch α β 1 = 2 * (α.re * β.im - α.im * β.re) := rfl
@[simp] theorem bloch_two (α β : ℂ) :
    bloch α β 2 = Complex.normSq α - Complex.normSq β := rfl

/-- **The two-qubit correlation identity.** -/
theorem bloch_inner_eq_proof (αa βa αb βb : ℂ)
    (ha : Complex.normSq αa + Complex.normSq βa = 1)
    (hb : Complex.normSq αb + Complex.normSq βb = 1) :
    2 * Complex.normSq (βa * αb - αa * βb)
      = 1 - (bloch αa βa 0 * bloch αb βb 0 + bloch αa βa 1 * bloch αb βb 1
          + bloch αa βa 2 * bloch αb βb 2) := by
  simp only [bloch_zero, bloch_one, bloch_two, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have h1 := ha
  have h2 := hb
  simp only [Complex.normSq_apply] at h1 h2
  nlinarith [h1, h2]

end QuantumMaxCutEnergy

open QuantumMaxCutEnergy in
theorem solution (αa βa αb βb : ℂ)
    (ha : Complex.normSq αa + Complex.normSq βa = 1)
    (hb : Complex.normSq αb + Complex.normSq βb = 1) :
    2 * Complex.normSq (βa * αb - αa * βb)
      = 1 - (bloch αa βa 0 * bloch αb βb 0 + bloch αa βa 1 * bloch αb βb 1
          + bloch αa βa 2 * bloch αb βb 2) :=
  QuantumMaxCutEnergy.bloch_inner_eq_proof αa βa αb βb ha hb

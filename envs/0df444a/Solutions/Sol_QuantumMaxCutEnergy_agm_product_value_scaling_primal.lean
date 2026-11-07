-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_product_value_scaling_primal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:26:48.577555+00:00
-- url     : https://prove2.me/submissions/687259cd-cdd3-40ec-a0cf-0ec048d8c871

import Mathlib

/-!
# The AGM value scaling, with no dual gap

`agm_product_value_scaling` (Proved) turns a primal–dual pair into the AGM bound: from
`0.954 S ≤ O`, `(O+W)/3 ≤ S`, `L ≤ S` and `S − L ≤ W/10⁴` it concludes
`0.953 (O+W)/3 ≤ 0.954 L`.

The gap hypothesis `S − L ≤ W/10⁴` forces `L` to track the *optimal* value `S`, hence to come with a
near-optimal dual certificate. This file removes it: the same conclusion follows from the **purely
primal** hypothesis

  `(0.953 / 0.954) * (O + W) / 3 ≤ L`

together with `L ≤ S`, which holds for *any* feasible point `X` with `L = obj X`. The factor is
exact — `0.954 · (0.953/0.954) = 0.953` — so nothing is lost.

Any `L` satisfying the old hypotheses satisfies the new one, because
`S ≥ (O+W)/3` and the gap is `W/10⁴`, far smaller than the `0.105%` slack between `0.953` and
`0.954`. So this is a strict weakening: it takes the primal–dual certificate off the critical path.
-/

open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **The AGM value scaling from a primal point alone.** -/
theorem agm_product_value_scaling_primal_proof (O W S L : ℝ)
    (hstruct : (O + W) / 3 ≤ S)
    (hgap : (0.954 : ℝ) * S ≤ O)
    (hL0 : 0 ≤ L) (hLS : L ≤ S)
    (hLlow : (0.953 / 0.954) * ((O + W) / 3) ≤ L) :
    0 ≤ (0.954 : ℝ) * L ∧
      (0.954 : ℝ) * L ≤ O ∧
        (0.953 : ℝ) * (O + W) / 3 ≤ (0.954 : ℝ) * L := by
  refine ⟨?_, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) hL0
  · exact (mul_le_mul_of_nonneg_left hLS (by norm_num)).trans hgap
  · have h := mul_le_mul_of_nonneg_left hLlow (by norm_num : (0 : ℝ) ≤ 0.954)
    have he : (0.954 : ℝ) * ((0.953 / 0.954) * ((O + W) / 3))
        = 0.953 * (O + W) / 3 := by
      field_simp
    linarith [h, he]

end QuantumMaxCutEnergy

open QuantumMaxCutEnergy in
theorem solution (O W S L : ℝ)
    (hstruct : (O + W) / 3 ≤ S)
    (hgap : (0.954 : ℝ) * S ≤ O)
    (hL0 : 0 ≤ L) (hLS : L ≤ S)
    (hLlow : (0.953 / 0.954) * ((O + W) / 3) ≤ L) :
    0 ≤ (0.954 : ℝ) * L ∧
      (0.954 : ℝ) * L ≤ O ∧
        (0.953 : ℝ) * (O + W) / 3 ≤ (0.954 : ℝ) * L :=
  QuantumMaxCutEnergy.agm_product_value_scaling_primal_proof O W S L hstruct hgap hL0 hLS hLlow

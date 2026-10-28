-- Prove2me | solution 1 for SolarNonOwn.BizChoice.compare_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:06:56.143995+00:00
-- url     : https://prove2.me/submissions/03f52e6f-4f6a-4343-bd2b-ca4d9c9f4970

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

open SolarNonOwn.BizChoice in
theorem solution (prm : Params) (hβ : 0 < prm.beta)
    (ht : 0 < prm.t) (htr : prm.t < prm.r) (hβr : prm.beta < prm.r) :
    A1 prm < A2 prm ∧ A2 prm < Acon prm := by
  have hr : 0 < prm.r := by linarith
  have hD : 0 < prm.r * (prm.r + prm.beta) + prm.beta * prm.t := by positivity
  have hE : 0 < prm.beta + prm.r := by positivity
  refine ⟨?_, ?_⟩
  · unfold A1 A2
    rw [div_lt_div_iff₀ hD hE]
    nlinarith [mul_pos hβ hr, mul_pos (mul_pos hβ hr) hr, mul_pos (mul_pos hβ hβ) hr]
  · unfold A2 Acon
    rw [Real.lt_sqrt (by positivity), div_pow, div_lt_div_iff₀ (by positivity) hD]
    have h1 : 0 < prm.beta * prm.r ^ 2 + prm.r ^ 3 + 2 * prm.beta * prm.r * prm.t
        + prm.t * prm.r ^ 2 := by positivity
    have e : prm.beta * (prm.r + prm.t) * (prm.beta + prm.r) ^ 2 -
        prm.beta ^ 2 * (prm.r * (prm.r + prm.beta) + prm.beta * prm.t) =
        prm.beta * (prm.beta * prm.r ^ 2 + prm.r ^ 3 + 2 * prm.beta * prm.r * prm.t
        + prm.t * prm.r ^ 2) := by ring
    nlinarith [mul_pos hβ h1]

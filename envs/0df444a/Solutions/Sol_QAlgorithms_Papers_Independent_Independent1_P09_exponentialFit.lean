-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.exponentialFit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:45:27.063385+00:00
-- url     : https://prove2.me/submissions/a2038317-5400-49e1-a06a-4f2b2e3b7f38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P09
open ErrorMitigation

/-- PDF pp.10–11, §XI: conditional exact exponential-model fit, not empirical ratio unbiasedness. -/


theorem solution (a decay e0 r : ℝ) (ha : 0 < a) (hdecay : 0 < decay)
    (he0 : 0 < e0) (hr : 1 < r) :
    (a*Real.exp (-decay*e0))^(r/(r-1)) *
      (a*Real.exp (-decay*(r*e0)))^(1/(1-r)) = a := by
  have hr1 : r - 1 ≠ 0 := by linarith
  have hr2 : 1 - r ≠ 0 := by linarith
  rw [Real.mul_rpow ha.le (Real.exp_pos _).le, Real.mul_rpow ha.le (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.exp_mul]
  have e1 : a ^ (r / (r - 1)) * Real.exp (-decay * e0 * (r / (r - 1))) *
      (a ^ (1 / (1 - r)) * Real.exp (-decay * (r * e0) * (1 / (1 - r)))) =
      (a ^ (r / (r - 1)) * a ^ (1 / (1 - r))) *
        Real.exp (-decay * e0 * (r / (r - 1)) + -decay * (r * e0) * (1 / (1 - r))) := by
    rw [Real.exp_add]; ring
  rw [e1, ← Real.rpow_add ha]
  have e2 : r / (r - 1) + 1 / (1 - r) = 1 := by
    field_simp
    ring
  have e3 : -decay * e0 * (r / (r - 1)) + -decay * (r * e0) * (1 / (1 - r)) = 0 := by
    field_simp
    ring
  rw [e2, e3, Real.rpow_one, Real.exp_zero, mul_one]


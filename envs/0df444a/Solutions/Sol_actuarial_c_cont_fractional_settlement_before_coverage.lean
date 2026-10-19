-- Prove2me | solution 1 for actuarial_c_cont_fractional_settlement_before_coverage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:54:28.633788+00:00
-- url     : https://prove2.me/submissions/63f99373-083a-4c59-aa1a-3e2c36a3064a

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_cont_fractionalSettlementPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (m h : ℕ) (delta t : ℝ)
    (ht : t < 0) :
    fractionalSettlementPV m h delta t = 0 := by
  unfold fractionalSettlementPV
  apply Finset.sum_eq_zero
  intro r _
  rw [if_neg]
  rintro ⟨h1, _⟩
  have : 0 ≤ fractionalTime m r := by unfold fractionalTime; positivity
  linarith


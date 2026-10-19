-- Prove2me | solution 1 for actuarial_c_cont_annual_grid_is_fractional_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:50:23.317003+00:00
-- url     : https://prove2.me/submissions/5dd5965d-0e9f-42a3-9095-ff50e5df7d05

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_cont_annualSettlementPV
import Definitions.Def_actuarial_c_cont_fractionalSettlementPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (h : ℕ) (delta t : ℝ) :
    fractionalSettlementPV 1 h delta t = annualSettlementPV h delta t := by
  unfold ActuarialAssurances.Continuous.annualSettlementPV  ActuarialAssurances.Continuous.fractionalSettlementPV  ActuarialAssurances.Continuous.fractionalTime <;> simp <;> ring


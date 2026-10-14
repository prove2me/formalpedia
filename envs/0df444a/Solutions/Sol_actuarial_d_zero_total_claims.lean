-- Prove2me | solution 1 for actuarial_d_zero_total_claims
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:40.107207+00:00
-- url     : https://prove2.me/submissions/d74bbacf-c24a-4e0a-b48d-6f7cf340131f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_totalValue
import Definitions.Def_actuarial_d_totalPath
import Definitions.Def_actuarial_d_annMemberSpouse
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : totalValue h n p d b rho 0 0 0 0 0 = annMemberSpouse h n p d b rho := by
  simp [expect, annMemberSpouse, annValue, annPath, onlyY, dead, alive, totalPath, tiePath, yFirstPath, xFirstPath, secondPath, firstPath, totalValue]

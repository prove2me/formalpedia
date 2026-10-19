-- Prove2me | solution 1 for actuarial_c_return_premium_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:04:51.441974+00:00
-- url     : https://prove2.me/submissions/cdbb10b3-c5be-4e9a-a093-11b04112c720

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_inc
import Definitions.Def_actuarial_c_returnBenefits

open ActuarialAssurances



theorem solution (h : ℕ) (v premium : ℝ) (p : ℕ → ℝ) : epv h v (returnBenefits premium) p=premium*epv h v inc p := by
  unfold epv path returnBenefits inc
  simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _; ring


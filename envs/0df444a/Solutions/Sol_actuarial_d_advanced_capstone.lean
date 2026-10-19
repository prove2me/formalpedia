-- Prove2me | solution 1 for actuarial_d_advanced_capstone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T14:55:22.48049+00:00
-- url     : https://prove2.me/submissions/601f5fab-c9b2-40ad-8735-f71291ae1121

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_advancedPath
import Definitions.Def_actuarial_d_deferGuaranteed
import Definitions.Def_actuarial_d_deferBlockedRev
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferTopup
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint
import Definitions.Def_actuarial_d_deferOverlap
import Definitions.Def_actuarial_d_totalValue
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Definitions.Def_actuarial_d_assureXSecond
import Definitions.Def_actuarial_d_assureYSecond
import Definitions.Def_actuarial_d_valid
import Theorems.Thm_actuarial_d_advanced_factor_reconciliation
import Theorems.Thm_actuarial_d_advanced_occupation_reconciliation
import Theorems.Thm_actuarial_d_advanced_specialises_without_guarantee
import Theorems.Thm_actuarial_d_first_assurance_partition
import Theorems.Thm_actuarial_d_second_assurance_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) (hp : valid h p) (hterm : a + n ≤ h+1) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) : (advancedValue h a n g p d b rho f s fx fy ft = deferGuaranteed h a n g p d b + rho * deferBlockedRev h a n g p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d) ∧ (advancedValue h a n g p d b rho f s fx fy ft = deferX h a n p d b + deferTopup h a n g p d b + rho * (deferY h a n p d b - deferJoint h a n p d b - deferOverlap h a n g p d b) + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d) ∧ (advancedValue h 0 n 0 p d b rho f s fx fy ft = totalValue h n p d b rho f s fx fy ft) ∧ (assureFirst h p d = assureXFirst h p d + assureYFirst h p d + assureTie h p d) ∧ (assureSecond h p d = assureXSecond h p d + assureYSecond h p d + assureTie h p d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact actuarial_d_advanced_occupation_reconciliation
      h a n g p d b rho f s fx fy ft
  · exact actuarial_d_advanced_factor_reconciliation
      h a n g p d b rho f s fx fy ft
  · exact actuarial_d_advanced_specialises_without_guarantee
      h n p d b rho f s fx fy ft
  · exact actuarial_d_first_assurance_partition h p d
  · exact actuarial_d_second_assurance_partition h p d

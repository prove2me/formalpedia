-- Prove2me | solution 1 for PI.WGB.twist_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:25.518867+00:00
-- url     : https://prove2.me/submissions/69321966-1769-4897-8c54-3ea6e876b392

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_NatWAntiC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (cF cE : ℤ) (d : ℕ) (hc : cE = cF + d) :
    a ^ cF * star (b ^ cF) * (star b * a) ^ d = a ^ cE * star (b ^ cE) := by
  subst hc
  rw [star_zpow₀, star_zpow₀, zpow_add₀ ha, zpow_add₀ (star_ne_zero.mpr hb), zpow_natCast, zpow_natCast,
    mul_pow]
  ring
end PI.WGB

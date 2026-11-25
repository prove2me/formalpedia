-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.le_exp_neg_one_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:14.061785+00:00
-- url     : https://prove2.me/submissions/843b844e-0c4d-4be0-89c4-d50ee03a227f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel WithZero
open PI PI.PinHostLoc PI.PinHostLoc.UnitaryGroupMassFormula
namespace PI.PinHostLoc.UnitaryGroupMassFormula
theorem _root_.solution {a : ℤᵐ⁰} (h : a < 1) : a ≤ exp (-1) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · rw [← WithZero.exp_log ha] at h ⊢
    have h' : WithZero.exp (WithZero.log a) < WithZero.exp (0 : ℤ) := by
      rwa [WithZero.exp_zero]
    rw [WithZero.exp_lt_exp] at h'
    rw [WithZero.exp_le_exp]
    omega
end PI.PinHostLoc.UnitaryGroupMassFormula

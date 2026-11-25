-- Prove2me | solution 1 for PI.GTS.norm_units_zpow_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:45.136611+00:00
-- url     : https://prove2.me/submissions/aaa10528-2170-459a-a018-ccd1f21fba75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTS
open Formalism.BasicNotions MvPolynomial
namespace PI.GTS
theorem _root_.solution (u : ℂˣ) (e : ℤ) :
    ‖((u ^ e : ℂˣ) : ℂ)‖ ^ 2 = ‖(u : ℂ)‖ ^ (2 * e) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring
end PI.GTS

-- Prove2me | solution 1 for PI.AmpRootJacW.mp_unitConj1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:22.296524+00:00
-- url     : https://prove2.me/submissions/ed55cf59-f1c2-4e1d-8001-a56aa29fa492

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
namespace PI.AmpRootJacW
theorem _root_.solution (c : ℂ) (hc : ‖c‖ = 1) : MeasurePreserving (fun x : ℂ => c * star x) volume volume := by
  let u : Circle := ⟨c, by simp [Submonoid.unitSphere, hc]⟩
  have h := ((Complex.conjLIE).trans (rotation u)).measurePreserving
  convert h using 1
  all_goals first
    | rfl
    | (funext x; simp only [LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply]; rfl)
end PI.AmpRootJacW

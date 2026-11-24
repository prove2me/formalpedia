-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GaugeFrame.blk_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:44.479539+00:00
-- url     : https://prove2.me/submissions/cec3d571-ec9e-4c78-8c74-994173f1e15b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameIso_MulFirstColumnOfUnitColumn
import Theorems.Thm_PI_UnitaryGroupMassFormula_GaugeFrame_low_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_GaugeFrame_blk_zero_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_GaugeFrame_blk_zero_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.GaugeFrame.low_apply
attribute [local simp] PI.UnitaryGroupMassFormula.GaugeFrame.blk_zero_zero
attribute [local simp] PI.UnitaryGroupMassFormula.GaugeFrame.blk_zero_succ

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GaugeFrame
open Matrix Formalism.UG
variable {S : Type} [CommRing S] (τ : S →+* S)
variable {m : ℕ}
namespace PI.UnitaryGroupMassFormula.GaugeFrame
theorem _root_.solution (c : S) (A : Matrix (Fin m) (Fin m) S) (i : Fin m) :
    blk c A i.succ 0 = 0 := by
  simp [blk]
end PI.UnitaryGroupMassFormula.GaugeFrame

-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GaugeFrame.low_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:43.746299+00:00
-- url     : https://prove2.me/submissions/576d7168-47b7-45b9-9a6f-2b330b19fe4f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameIso_MulFirstColumnOfUnitColumn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GaugeFrame
open Matrix Formalism.UG
variable {S : Type} [CommRing S] (τ : S →+* S)
variable {m : ℕ}
namespace PI.UnitaryGroupMassFormula.GaugeFrame
theorem _root_.solution (K : Matrix (Fin (m + 1)) (Fin (m + 1)) S) (i j : Fin m) :
    low K i j = K i.succ j.succ := rfl
end PI.UnitaryGroupMassFormula.GaugeFrame

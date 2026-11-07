-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.planeFrame_eq_xy_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:22:35.880515+00:00
-- url     : https://prove2.me/submissions/7980ca35-a888-4664-b646-c72f23696090

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (p q : Plane) :
    planeFrame p q = .xy ↔ q = p := by
  cases p <;> cases q <;> decide
end QEC.Coding.PeriodicCubical4

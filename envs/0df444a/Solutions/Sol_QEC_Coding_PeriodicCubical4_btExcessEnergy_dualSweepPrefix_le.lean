-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.btExcessEnergy_dualSweepPrefix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:02:40.191003+00:00
-- url     : https://prove2.me/submissions/9c0f1a34-ea0d-42b8-8264-d159a4a0a10e

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualLoopLength_sweepPrefix_le
import Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_dualMembrane


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).btExcessEnergy
        (dualMembraneError (dualSweepPrefix x y n)) ≤ 64 * L := by
  rw [btExcessEnergy_dualMembrane]
  have h := Nat.mul_le_mul_left 2
    (dualLoopLength_sweepPrefix_le x y n hn)
  omega
end QEC.Coding.PeriodicCubical4

-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.btExcessEnergy_primalSweepPrefix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:02:33.042047+00:00
-- url     : https://prove2.me/submissions/df215219-8ce6-43c1-a189-3f63c82f20b2

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalLoopLength_sweepPrefix_le
import Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_primalMembrane


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).btExcessEnergy
        (primalMembraneError (primalSweepPrefix z w n)) ≤ 64 * L := by
  rw [btExcessEnergy_primalMembrane]
  have h := Nat.mul_le_mul_left 2
    (primalLoopLength_sweepPrefix_le z w n hn)
  omega
end QEC.Coding.PeriodicCubical4

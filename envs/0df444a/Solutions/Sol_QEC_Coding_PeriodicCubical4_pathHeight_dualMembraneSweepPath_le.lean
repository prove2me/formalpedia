-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.pathHeight_dualMembraneSweepPath_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:08:53.366308+00:00
-- url     : https://prove2.me/submissions/6865261b-403a-460a-81d5-edd147d1885c

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_dualMembraneSweepPath_stateAt_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (x y : ZMod L) :
    (toricHamiltonian (L := L)).pathHeight
        (dualMembraneSweepPath x y) ≤ 64 * L := by
  rw [pathHeight]
  apply Finset.sup_le
  intro n hn
  apply btExcessEnergy_dualMembraneSweepPath_stateAt_le x y n
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hn)
end QEC.Coding.PeriodicCubical4

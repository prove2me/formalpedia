-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualSweepRegion_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:44:54.983198+00:00
-- url     : https://prove2.me/submissions/f7f5199a-2b2c-4872-933b-3a8541c1ca78

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (x y : ZMod L) (n : Nat) :
    dualSweepRegion x y n ⊆ (dualSweepPlaquettes x y).toFinset := by
  intro q hq
  rw [dualSweepRegion, List.mem_toFinset] at hq
  rw [List.mem_toFinset]
  exact List.mem_of_mem_take hq
end QEC.Coding.PeriodicCubical4

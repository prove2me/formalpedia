-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalSweepRegion_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:44:49.70377+00:00
-- url     : https://prove2.me/submissions/da8eca64-ce6d-4662-98cb-30c41b2ddf45

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
theorem _root_.solution (z w : ZMod L) (n : Nat) :
    primalSweepRegion z w n ⊆ (primalSweepPlaquettes z w).toFinset := by
  intro q hq
  rw [primalSweepRegion, List.mem_toFinset] at hq
  rw [List.mem_toFinset]
  exact List.mem_of_mem_take hq
end QEC.Coding.PeriodicCubical4

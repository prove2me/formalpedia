-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.card_dualSweepFrontier_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:53:05.725109+00:00
-- url     : https://prove2.me/submissions/c95b3518-ba74-488e-b0dc-dfda08379973

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Theorems.Thm_QEC_Coding_PeriodicCubical4_card_sweepSiteFrontier_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (x y : ZMod L) (n : Nat) :
    (dualSweepFrontier x y n).card ≤ 4 * L := by
  exact Finset.card_image_le.trans (card_sweepSiteFrontier_le L n)
end QEC.Coding.PeriodicCubical4

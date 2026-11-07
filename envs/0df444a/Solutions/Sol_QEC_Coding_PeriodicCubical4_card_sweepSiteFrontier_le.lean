-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.card_sweepSiteFrontier_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:45:01.220111+00:00
-- url     : https://prove2.me/submissions/499ca0b7-2c2f-430f-8ee2-a4c61558440b

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_card_movingFrontier_le
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_card_seamFrontier_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (L n : Nat) :
    (sweepSiteFrontier L n).card ≤ 4 * L := by
  calc
    (sweepSiteFrontier L n).card ≤
        (StripGeometry.movingFrontier L 0 L (n / L) 2).card +
          (StripGeometry.seamFrontier L 0 L 2).card :=
      Finset.card_union_le ..
    _ ≤ L * 2 + L * 2 :=
      Nat.add_le_add
        (StripGeometry.card_movingFrontier_le L 0 L (n / L) 2)
        (StripGeometry.card_seamFrontier_le L 0 L 2)
    _ = 4 * L := by omega
end QEC.Coding.PeriodicCubical4

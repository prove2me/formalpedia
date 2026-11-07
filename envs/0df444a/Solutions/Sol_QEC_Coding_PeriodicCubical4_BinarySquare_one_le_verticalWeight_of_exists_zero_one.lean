-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.BinarySquare.one_le_verticalWeight_of_exists_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:55:04.455793+00:00
-- url     : https://prove2.me/submissions/ad28ee62-255e-4039-bd42-852a10d2406b

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_one_le_horizontalWeight_of_exists_zero_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare
namespace QEC.Coding.PeriodicCubical4.BinarySquare
theorem _root_.solution {n : Nat} (g : Grid n)
    (x : Fin n) (hzero : ∃ y, g y x = 0) (hone : ∃ y, g y x = 1) :
    1 ≤ HammingWeight (verticalDerivative g x) := by
  let gt : Grid n := fun y x => g x y
  have htranspose : verticalDerivative g x = horizontalDerivative gt x := by
    rfl
  rw [htranspose]
  exact one_le_horizontalWeight_of_exists_zero_one gt x hzero hone
end QEC.Coding.PeriodicCubical4.BinarySquare

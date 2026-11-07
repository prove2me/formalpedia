-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.BinarySquare.one_le_horizontalWeight_of_exists_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:52:31.652648+00:00
-- url     : https://prove2.me/submissions/82a4c291-b66b-42f5-a98a-9cfe71e8675a

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_eq_zero_of_horizontalDerivative_eq_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
open QEC.Coding.PeriodicCubical4.BinarySquare
namespace QEC.Coding.PeriodicCubical4.BinarySquare
theorem _root_.solution {n : Nat} (g : Grid n)
    (y : Fin n) (hzero : ∃ x, g y x = 0) (hone : ∃ x, g y x = 1) :
    1 ≤ HammingWeight (horizontalDerivative g y) := by
  by_contra hnot
  have hweight : HammingWeight (horizontalDerivative g y) = 0 := by omega
  have hderiv : horizontalDerivative g y = 0 :=
    (HammingWeight_eq_zero_iff _).mp hweight
  obtain ⟨x₀, hx₀⟩ := hzero
  obtain ⟨x₁, hx₁⟩ := hone
  have := eq_zero_of_horizontalDerivative_eq_zero g y hderiv x₀ x₁
  rw [hx₀, hx₁] at this
  exact zero_ne_one this
end QEC.Coding.PeriodicCubical4.BinarySquare

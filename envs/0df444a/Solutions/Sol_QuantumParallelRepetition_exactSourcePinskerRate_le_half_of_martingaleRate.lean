-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourcePinskerRate_le_half_of_martingaleRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/4fe8c98f-9b27-45da-b877-7cc2d0bb614b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactSourceClassicalInformationRate_le_three_martingaleRate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    {rateTolerance : ℝ} (rate_nonnegative : 0 ≤ rateTolerance)
    (rate_bound :
      martingaleRate G n S D ≤ rateTolerance ^ 2 / 8) :
    exactSourcePinskerRate G n S D ≤ rateTolerance / 2 := by
  unfold exactSourcePinskerRate
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have information :=
      exactSourceClassicalInformationRate_le_three_martingaleRate
        G n S D positive
    nlinarith
end QuantumParallelRepetition

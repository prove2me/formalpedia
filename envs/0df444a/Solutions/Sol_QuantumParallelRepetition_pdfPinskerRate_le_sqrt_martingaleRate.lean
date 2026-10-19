-- Prove2me | solution 1 for QuantumParallelRepetition.pdfPinskerRate_le_sqrt_martingaleRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/5b597729-35ee-4d7c-b885-ad573eaabd0c

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactSourceClassicalInformationRate_le_three_martingaleRate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactSourcePinskerRate G n S D ≤
      Real.sqrt ((3 / 2 : ℝ) * martingaleRate G n S D) := by
  unfold exactSourcePinskerRate
  apply Real.sqrt_le_sqrt
  have information :=
    exactSourceClassicalInformationRate_le_three_martingaleRate
      G n S D positive
  nlinarith
end QuantumParallelRepetition

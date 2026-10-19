-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourceOneGameRounding_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/757c7d68-d5dc-4bf1-967c-e0ab16bc565b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourceOneGameRounding_uniform_of_small
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalRounding_exists_small

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
namespace QuantumParallelRepetition
theorem _root_.solution :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B)
        (n : ℕ) (S : Strategy (G.repeat n))
        (D : Finset (Fin n)),
        0 < (Finset.univ \ D).card →
        0 < repeatedPostselectionMass G n S D →
        ∀ (alpha gamma : ℝ),
          0 < alpha → alpha ≤ 1 → 0 < gamma →
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D <
            (1 - entangledValue G) / 2 →
          ∃ rounded : Strategy G,
            roundedWinningLowerBound (1 - entangledValue G)
                K alpha (martingaleRate G n S D)
                (exactSourcePinskerRate G n S D + gamma) ≤
              rounded.winProbability :=
  unconditionalSourceOneGameRounding_uniform_of_small
    unconditionalSourcePhysicalRounding_exists_small
end QuantumParallelRepetition

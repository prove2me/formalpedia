-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalRounding_exists_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/f686ddae-8fcf-4f72-9fd7-ed89e23013c3

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalRounding_smallRoundedLower_of_stoppedVerifier
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingData_exists_stoppedVerifier

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
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (failure :
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D <
        (1 - entangledValue G) / 2) :
    ∃ rounded : Strategy G,
      roundedWinningLowerBound
          (1 - entangledValue G)
          unconditionalSourcePhysicalRoundingUniversalConstant
          alpha (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + gamma) ≤
        rounded.winProbability := by
  obtain ⟨deviation, clipping, rounded,
      deviation_bound, clipping_bound, stopped⟩ :=
    unconditionalActualFairSourceRoundingData_exists_stoppedVerifier
      G n S D remaining positive alpha gamma
      alpha_positive alpha_bounded gamma_positive small failure
  refine ⟨rounded, ?_⟩
  exact
    unconditionalSourcePhysicalRounding_smallRoundedLower_of_stoppedVerifier
      G n S D remaining positive alpha gamma deviation clipping
      alpha_positive alpha_bounded gamma_positive small
      deviation_bound clipping_bound rounded stopped
end QuantumParallelRepetition

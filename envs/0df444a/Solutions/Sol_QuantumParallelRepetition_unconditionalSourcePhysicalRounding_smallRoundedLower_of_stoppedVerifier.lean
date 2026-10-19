-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalRounding_smallRoundedLower_of_stoppedVerifier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/e3070f67-d9d0-496b-8ebd-54d4b46020bf

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalRounding_smallRoundedLower

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha gamma deviation clipping : ℝ)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * martingaleRate G n S D +
          8 * (3 * alpha ^ (1 / 3 : ℝ) / 2))
    (rounded : Strategy G)
    (stopped_verifier :
      1 - (1 - entangledValue G) / 2 -
          5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt deviation + 2 * Real.sqrt clipping) ≤
        rounded.winProbability) :
    roundedWinningLowerBound (1 - entangledValue G)
        unconditionalSourcePhysicalRoundingUniversalConstant
        alpha (martingaleRate G n S D)
        (exactSourcePinskerRate G n S D + gamma) ≤
      rounded.winProbability := by
  apply unconditionalSourcePhysicalRounding_smallRoundedLower
    G n S D remaining positive alpha gamma deviation clipping
    alpha_positive alpha_bounded gamma_positive small
    actual_deviation actual_clipping rounded
  nlinarith [Real.sqrt_nonneg clipping,
    Real.sqrt_nonneg (8 * martingaleRate G n S D)]
end QuantumParallelRepetition

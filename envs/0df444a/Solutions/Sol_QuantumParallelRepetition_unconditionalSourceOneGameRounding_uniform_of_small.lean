-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourceOneGameRounding_uniform_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/9ded2d49-9b27-4c92-ace3-4618f3cb50ec

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalRoundingUniversalConstant_ge
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalRounding_exists_large

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
    (small_rounding :
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B)
        (n : ℕ) (S : Strategy (G.repeat n))
        (D : Finset (Fin n)),
        0 < (Finset.univ \ D).card →
        0 < repeatedPostselectionMass G n S D →
        ∀ (alpha gamma : ℝ),
          0 < alpha → alpha ≤ 1 → 0 < gamma →
          64 * Real.sqrt (martingaleRate G n S D) +
              alpha ^ (1 / 3 : ℝ) ≤ 1 →
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D <
            (1 - entangledValue G) / 2 →
          ∃ rounded : Strategy G,
            roundedWinningLowerBound (1 - entangledValue G)
                unconditionalSourcePhysicalRoundingUniversalConstant
                alpha (martingaleRate G n S D)
                (exactSourcePinskerRate G n S D + gamma) ≤
              rounded.winProbability) :
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
              rounded.winProbability := by
  refine ⟨unconditionalSourcePhysicalRoundingUniversalConstant,
    ?_, ?_⟩
  · linarith [unconditionalSourcePhysicalRoundingUniversalConstant_ge]
  intro X Y A B _ _ _ _ G n S D remaining positive
    alpha gamma alpha_positive alpha_bounded gamma_positive failure
  by_cases small :
      64 * Real.sqrt (martingaleRate G n S D) +
        alpha ^ (1 / 3 : ℝ) ≤ 1
  · exact small_rounding G n S D remaining positive alpha gamma
      alpha_positive alpha_bounded gamma_positive small failure
  · exact unconditionalSourcePhysicalRounding_exists_large
      G n S D remaining positive
      unconditionalSourcePhysicalRoundingUniversalConstant
      alpha gamma
      unconditionalSourcePhysicalRoundingUniversalConstant_ge
      alpha_positive alpha_bounded gamma_positive (lt_of_not_ge small)
end QuantumParallelRepetition

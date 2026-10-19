-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalRounding_exists_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/55f2996d-5d78-481e-ad36-f129755b68ad

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_Strategy_winProbability_nonneg
import Theorems.Thm_QuantumParallelRepetition_entangledValue_le_one
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalRounding_largeVerifierBound

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
    (K alpha gamma : ℝ)
    (constant : 128 ≤ K)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (gamma_positive : 0 < gamma)
    (large : 1 < 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ)) :
    ∃ rounded : Strategy G,
      roundedWinningLowerBound (1 - entangledValue G)
          K alpha (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + gamma) ≤
        rounded.winProbability := by
  classical
  obtain ⟨alice, bob⟩ :=
    exactSourceAnswerTypes_nonempty_of_remaining
      G n S D remaining
  let rounded : Strategy G := pdfConstantStrategy G
    (Classical.choice alice) (Classical.choice bob)
  refine ⟨rounded, ?_⟩
  have eta_nonnegative :=
    martingaleRate_nonneg G n S D remaining positive
  have epsilon_nonnegative : 0 ≤ 1 - entangledValue G := by
    linarith [entangledValue_le_one G]
  have pinsker_nonnegative :
      0 ≤ exactSourcePinskerRate G n S D := by
    unfold exactSourcePinskerRate
    positivity
  have source_bound :=
    unconditionalSourcePhysicalRounding_largeVerifierBound
      K (martingaleRate G n S D) alpha
      (exactSourcePinskerRate G n S D + gamma)
      (1 - entangledValue G)
      constant eta_nonnegative alpha_positive alpha_bounded
      (by linarith) epsilon_nonnegative large
  exact source_bound.trans rounded.winProbability_nonneg
end QuantumParallelRepetition

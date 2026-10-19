-- Prove2me | solution 1 for QuantumParallelRepetition.pdfFixedExponentialBound_of_sourceEquationTwentyNine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/e09cc1ea-4822-4b54-acbf-5ff8441669dd

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_source_equation_twenty_nine_contradiction
import Theorems.Thm_QuantumParallelRepetition_pdfExistsRepeatedStrategyAboveExponential

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (d : ℝ)
    (construct :
      ∀ S : Strategy (G.repeat n),
        Real.exp (-d * (n : ℝ)) < S.winProbability →
          ∃ (rounded : Strategy G) (K₀ α η lam : ℝ),
            roundedWinningLowerBound (1 - entangledValue G)
                K₀ α η lam ≤ rounded.winProbability ∧
              totalSamplingLoss K₀ α η lam <
                (1 - entangledValue G) / 2) :
    repeatedEntangledValue G n ≤ Real.exp (-d * (n : ℝ)) := by
  by_contra not_bound
  have failure :
      Real.exp (-d * (n : ℝ)) < repeatedEntangledValue G n :=
    lt_of_not_ge not_bound
  obtain ⟨S, winning⟩ :=
    pdfExistsRepeatedStrategyAboveExponential G n d failure
  obtain ⟨rounded, K₀, α, η, lam, bound, error⟩ :=
    construct S winning
  exact source_equation_twenty_nine_contradiction
    G rounded K₀ α η lam bound error
end QuantumParallelRepetition

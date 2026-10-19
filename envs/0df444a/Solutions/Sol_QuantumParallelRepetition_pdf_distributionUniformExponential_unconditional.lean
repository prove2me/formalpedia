-- Prove2me | solution 1 for QuantumParallelRepetition.pdf_distributionUniformExponential_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/5e0d1619-14ed-4006-ad92-e8baab3ef2dc

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdf_distributionUniformExponential_of_uniform_source_rounding
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourceOneGameRounding_uniform

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) :=
  pdf_distributionUniformExponential_of_uniform_source_rounding
    unconditionalSourceOneGameRounding_uniform
end QuantumParallelRepetition

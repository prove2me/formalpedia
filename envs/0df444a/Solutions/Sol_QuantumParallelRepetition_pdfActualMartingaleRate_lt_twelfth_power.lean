-- Prove2me | solution 1 for QuantumParallelRepetition.pdfActualMartingaleRate_lt_twelfth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/dc8b796b-8421-4e29-957a-2340ad3002cf

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfQuantitativeEntropyRate_lt_twelfth_power
import Theorems.Thm_QuantumParallelRepetition_pdfPostselectionLogCost_lt_of_exponential

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
    (Bqs ε ell : ℝ)
    (constant : 1 ≤ Bqs)
    (gap : 0 < ε)
    (unit : ε ≤ 1)
    (alphabet : 0 ≤ ell)
    (alphabet_eq : ell =
      Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))
    (length : 0 < n)
    (remaining :
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ))
    (above :
      Real.exp
        (-pdfGapRate Bqs ε ell * (n : ℝ)) <
        repeatedPostselectionMass G n S D)
    (conditioned :
      (D.card : ℝ) <
        pdfGapRate Bqs ε ell * (n : ℝ) /
          pdfConditioningTolerance ε) :
    martingaleRate G n S D < (ε / (4 * Bqs)) ^ 12 := by
  have postselection :=
    pdfPostselectionLogCost_lt_of_exponential
      G n S D (pdfGapRate Bqs ε ell) above
  have actual := pdfQuantitativeEntropyRate_lt_twelfth_power
    constant gap unit alphabet length remaining postselection conditioned
  simpa [martingaleRate, answerLogCost, alphabet_eq]
    using actual
end QuantumParallelRepetition

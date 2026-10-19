-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_square_of_matching_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/eb0154dc-9581-47e9-adcb-c8bf4352596e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_coefficientTranscendenceDegree_ge_square_of_algebraicIndependent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_algebraicIndependent_of_prodCongr
import Theorems.Thm_PermanentFormulaLowerBound_exists_matchingDiagonal_prodCongr

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n ell m : ℕ} (hn : n = (ell + ell) + m)
    (d : (Fin ell ⊕ Fin ell) ↪ Fin n × Fin n)
    (hrows : Function.Injective (fun y => (d y).1))
    (hcols : Function.Injective (fun y => (d y).2))
    (hind : AlgebraicIndependent ℂ
      (fun de : Fin m × Fin m =>
        coefficientPolynomial
          (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
          (matchingSquarefreeMonomial
            (matchingBitCoefficientSet ell m de)))) :
    ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d) := by
  subst n
  obtain ⟨r, c, he⟩ :=
    exists_matchingDiagonal_prodCongr d hrows hcols
  apply coefficientTranscendenceDegree_ge_square_of_algebraicIndependent
    (matchingMarkedPermanent d)
    (fun de : Fin m × Fin m =>
      matchingSquarefreeMonomial (matchingBitCoefficientSet ell m de))
  exact matchingMarkedPermanent_algebraicIndependent_of_prodCongr
    (matchingDiagonalEmbedding ell m) d r c he _ hind
end PermanentFormulaLowerBound

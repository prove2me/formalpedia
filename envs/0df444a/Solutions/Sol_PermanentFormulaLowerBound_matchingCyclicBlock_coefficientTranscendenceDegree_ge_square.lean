-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/6e754f91-fb29-40be-972a-d55c2f348aed

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingCyclicDiagonalEmbedding_fst_injective
import Theorems.Thm_PermanentFormulaLowerBound_matchingCyclicDiagonalEmbedding_snd_injective
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n ell m : ℕ}
    (hk : 0 < 2 * ell) (hn : n = (ell + ell) + m)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
      (matchingMarkedPermanent (matchingCyclicDiagonalEmbedding hk t j)) :=
  matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
    hn (matchingCyclicDiagonalEmbedding hk t j)
    (matchingCyclicDiagonalEmbedding_fst_injective hk t j)
    (matchingCyclicDiagonalEmbedding_snd_injective hk t j)
    hm hroom
end PermanentFormulaLowerBound

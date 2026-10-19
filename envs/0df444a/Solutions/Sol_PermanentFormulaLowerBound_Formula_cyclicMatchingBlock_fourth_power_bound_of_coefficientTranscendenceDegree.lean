-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/671a7198-7f93-48be-8b56-f300009dc126

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_cyclicMatchingBlock_fourth_power_bound
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_cyclicMatchingBlock_fourth_power_bound
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedFinset_matchingCyclicDiagonalEmbedding
import Theorems.Thm_PermanentFormulaLowerBound_Formula_matching_block_four_leaves_of_coefficientTranscendenceDegree

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    {n ell m : ℕ}
    (hk : 0 < 2 * ell) (hkn : 2 * ell ≤ n) (hhalf : n ≤ 2 * m)
    (f : Formula (Fin n × Fin n) ℂ)
    (hf : eval f = permanentPolynomial n)
    (hcertificate : ∀ x : Fin n × Fin (n / (2 * ell)),
      ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
        (matchingMarkedPermanent
          (matchingCyclicDiagonalEmbedding hk x.1 x.2))) :
    n ^ 4 ≤ 32 * (2 * ell) * variableLeaves f := by
  classical
  have hell : 0 < ell := by omega
  letI : Nonempty (Fin ell ⊕ Fin ell) :=
    ⟨.inl ⟨0, hell⟩⟩
  apply cyclicMatchingBlock_fourth_power_bound hk hkn m hhalf f
  intro x
  have h := matching_block_four_leaves_of_coefficientTranscendenceDegree
    (matchingCyclicDiagonalEmbedding hk x.1 x.2) f hf
      (hcertificate x)
  simpa only [matchingMarkedFinset_matchingCyclicDiagonalEmbedding]
    using h
end PermanentFormulaLowerBound.Formula

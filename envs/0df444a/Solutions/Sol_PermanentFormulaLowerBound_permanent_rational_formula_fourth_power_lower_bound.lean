-- Prove2me | solution 1 for PermanentFormulaLowerBound.permanent_rational_formula_fourth_power_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/1b1ad22e-d4d2-4acd-b3c0-b8a68a0ddd51

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_five_le_clog_two
import Theorems.Thm_PermanentFormulaLowerBound_matching_block_size_le_half
import Theorems.Thm_PermanentFormulaLowerBound_matching_external_size_ge_block_add_one
import Theorems.Thm_PermanentFormulaLowerBound_matching_external_size_le_two_pow
import Theorems.Thm_PermanentFormulaLowerBound_Formula_cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
import Theorems.Thm_PermanentFormulaLowerBound_matchingCyclicBlock_coefficientTranscendenceDegree_ge_square

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} (hn : 32 ≤ n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : RationalFormula.Valid f)
    (hf : RationalFormula.eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    n ^ 4 ≤ 48 * (2 * Nat.clog 2 n) *
      RationalFormula.variableLeaves f := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let ell : ℕ := Nat.clog 2 n
  let m : ℕ := n - 2 * ell
  have hell : 5 ≤ ell := by
    simpa [ell] using five_le_clog_two hn
  have hk : 0 < 2 * ell := by omega
  have hblockhalf : 2 * ell ≤ n / 2 := by
    simpa [ell] using matching_block_size_le_half hn
  have hkn : 2 * ell ≤ n := by omega
  have hhalf : n ≤ 2 * m := by
    dsimp [m]
    omega
  have hdecomp : n = (ell + ell) + m := by
    dsimp [m]
    omega
  have hm : m ≤ 2 ^ ell := by
    simpa [ell, m] using
      (matching_external_size_le_two_pow (n := n))
  have hroom : 2 * ell < m := by
    have h := matching_external_size_ge_block_add_one hn
    dsimp [ell, m]
    omega
  have hcertificate :
      ∀ x : Fin n × Fin (n / (2 * ell)),
        ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
          (matchingMarkedPermanent
            (matchingCyclicDiagonalEmbedding hk x.1 x.2)) := by
    intro x
    exact matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
      hk hdecomp hm hroom x.1 x.2
  have hfour :=
    RationalFormula.cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
      hk hkn hhalf f hvalid hf hcertificate
  simpa [ell] using hfour
end PermanentFormulaLowerBound

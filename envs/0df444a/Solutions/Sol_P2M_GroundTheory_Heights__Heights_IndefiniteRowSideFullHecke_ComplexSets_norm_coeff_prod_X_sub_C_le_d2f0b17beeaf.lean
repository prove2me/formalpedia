-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_coeff_prod_X_sub_C_le_d2f0b17beeaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:53.084998+00:00
-- url     : https://prove2.me/submissions/8ff34d06-4044-46a7-9224-1fbaf51b37eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_X_sub_C_mul_zero_4704917d4fbc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_X_sub_C_mul_succ_64640c148516

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) {M : ℝ}
    (hM1 : 1 ≤ M) (ha : ∀ i ∈ s, ‖a i‖ ≤ M) :
    ∀ n, ‖(∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff n‖ ≤ (2 * M) ^ s.card := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
    split_ifs <;> simp
  | insert i s hi ih =>
    have hai : ‖a i‖ ≤ M := ha i (Finset.mem_insert_self i s)
    have ih' := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hB : 0 ≤ (2 * M) ^ s.card := pow_nonneg (by linarith) _
    intro n
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    cases n with
    | zero =>
      rw [coeff_X_sub_C_mul_zero, norm_mul, norm_neg]
      nlinarith [ih' 0, norm_nonneg (a i), norm_nonneg ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff 0)]
    | succ n =>
      rw [coeff_X_sub_C_mul_succ]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      nlinarith [ih' n, ih' (n + 1), norm_nonneg (a i),
        norm_nonneg ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff (n + 1))]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

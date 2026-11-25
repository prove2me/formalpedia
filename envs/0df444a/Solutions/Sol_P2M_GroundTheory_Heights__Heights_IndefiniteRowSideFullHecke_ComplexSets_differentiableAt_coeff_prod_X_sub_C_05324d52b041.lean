-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableAt_coeff_prod_X_sub_C_05324d52b041
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:48.302275+00:00
-- url     : https://prove2.me/submissions/ca3e5b14-2c14-4e5f-9d98-e160e7b56de7

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (a : ι → E → ℂ) (x : E) (ha : ∀ i ∈ s, DifferentiableAt ℂ (a i) x) :
    ∀ n, DifferentiableAt ℂ (fun x => (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i x))).coeff n) x := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert i s hi ih =>
    have hai : DifferentiableAt ℂ (a i) x := ha i (Finset.mem_insert_self i s)
    have ih' := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    intro n
    simp only [Finset.prod_insert hi]
    cases n with
    | zero =>
      simp only [coeff_X_sub_C_mul_zero]
      exact hai.neg.mul (ih' 0)
    | succ n =>
      simp only [coeff_X_sub_C_mul_succ]
      exact (ih' n).sub (hai.mul (ih' (n + 1)))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

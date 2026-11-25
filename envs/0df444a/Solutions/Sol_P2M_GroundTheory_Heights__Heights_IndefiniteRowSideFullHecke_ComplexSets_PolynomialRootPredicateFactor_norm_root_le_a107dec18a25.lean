-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_norm_root_le_a107dec18a25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:32:08.308832+00:00
-- url     : https://prove2.me/submissions/5e9e0bae-7b25-4c7e-93d2-54c52a948464

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor

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
open Polynomial Filter Topology Classical
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
theorem _root_.solution {N : ℕ} (c : Fin N → ℂ) (τ : ℂ) (h : τ ^ N + ∑ j, c j * τ ^ (j : ℕ) = 0) :
    ‖τ‖ ≤ 1 + ∑ j, ‖c j‖ := by
  have hs : 0 ≤ ∑ j, ‖c j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  by_cases h1 : ‖τ‖ ≤ 1
  · linarith
  push Not at h1
  cases N with
  | zero => simp at h
  | succ n =>
    have key : ‖τ‖ ^ (n + 1) ≤ (∑ j, ‖c j‖) * ‖τ‖ ^ n := by
      have e : τ ^ (n + 1) = -∑ j, c j * τ ^ (j : ℕ) := eq_neg_of_add_eq_zero_left h
      rw [← norm_pow, e, norm_neg, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1.le (Nat.lt_succ_iff.1 j.2)) (norm_nonneg _)
    have hpos : 0 < ‖τ‖ ^ n := pow_pos (by linarith) n
    rw [pow_succ, mul_comm (∑ j, ‖c j‖)] at key
    have := le_of_mul_le_mul_left key hpos
    linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor

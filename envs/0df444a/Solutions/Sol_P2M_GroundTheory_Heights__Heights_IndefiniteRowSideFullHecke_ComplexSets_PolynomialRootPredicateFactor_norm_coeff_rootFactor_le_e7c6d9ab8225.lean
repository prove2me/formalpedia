-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_norm_coeff_rootFactor_le_e7c6d9ab8225
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:45.284132+00:00
-- url     : https://prove2.me/submissions/7ddd72fc-feb4-428c-aa1a-6dcb9d2c5ada

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_fiberPoly_card_roots_f4bf3eaf143a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_mem_roots_fiberPoly_501f147fc65c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_rootFactor_monic_c06104680060
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_rootFactor_natDegree_3454157c1a46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_norm_root_le_a107dec18a25

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
theorem _root_.solution {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (Q : ℂ → Prop)
    (k : ℕ) : ‖(rootFactor (fiberPoly a t) Q).coeff k‖ ≤ (1 + ∑ j, ‖a j t‖) ^ N * 2 ^ N := by
  have hR : 1 ≤ 1 + ∑ j, ‖a j t‖ := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hroots : ∀ z ∈ ((rootFactor (fiberPoly a t) Q).map (RingHom.id ℂ)).roots, ‖z‖ ≤ 1 + ∑ j, ‖a j t‖ := by
    intro z hz
    rw [Polynomial.map_id, rootFactor, roots_multiset_prod_X_sub_C, Multiset.mem_filter] at hz
    exact norm_root_le _ z ((mem_roots_fiberPoly a t z).1 hz.1)
  have h := coeff_le_of_roots_le k (rootFactor_monic _ Q) (IsAlgClosed.splits _) hroots
  rw [Polynomial.map_id] at h
  have hdeg : (rootFactor (fiberPoly a t) Q).natDegree ≤ N := by
    rw [rootFactor_natDegree]
    exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (fiberPoly_card_roots a t).le
  refine h.trans (mul_le_mul (pow_le_pow_right₀ hR (by omega)) ?_ (by positivity) (by positivity))
  exact_mod_cast (Nat.choose_le_two_pow _ k).trans (Nat.pow_le_pow_right two_pos hdeg)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor

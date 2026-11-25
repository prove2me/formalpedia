-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_exists_root_9ba640ff292c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:57.268621+00:00
-- url     : https://prove2.me/submissions/c2360890-4b8f-4cef-8d81-bf3228d9131b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedPointsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormSheetedPointsNear

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
namespace PrimitiveFormSheetedPointsNear
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) (c : Fin n → ℂ) :
    ∃ τ : ℂ, τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0 := by
  set p : Polynomial ℂ := Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hp
  have hlt : (∑ j : Fin n, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).degree < (Polynomial.X ^ n : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j _ => ?_
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 j.isLt)
  have hdeg : p.degree = n := by
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  obtain ⟨τ, hτ⟩ := Complex.exists_root (f := p) (by rw [hdeg]; exact_mod_cast Nat.pos_of_ne_zero hn)
  exact ⟨τ, by simpa [p, Polynomial.eval_finsetSum] using hτ⟩
end PrimitiveFormSheetedPointsNear
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

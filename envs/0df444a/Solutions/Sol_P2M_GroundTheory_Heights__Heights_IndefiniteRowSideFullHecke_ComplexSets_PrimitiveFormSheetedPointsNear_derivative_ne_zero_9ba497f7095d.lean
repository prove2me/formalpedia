-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedPointsNear_derivative_ne_zero_9ba497f7095d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:33.426295+00:00
-- url     : https://prove2.me/submissions/db347ba6-ee79-4d5f-b9f6-359e7761be93

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
theorem _root_.solution (n : ℕ) (c : Fin n → ℂ) (τ : ℂ)
    (hs : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hτ : τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0) :
    (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 := by
  have h0 : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).eval τ = 0 := by
    simpa [Polynomial.eval_finsetSum] using hτ
  exact hs.eval₂_derivative_ne_zero (RingHom.id ℂ) h0
end PrimitiveFormSheetedPointsNear
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

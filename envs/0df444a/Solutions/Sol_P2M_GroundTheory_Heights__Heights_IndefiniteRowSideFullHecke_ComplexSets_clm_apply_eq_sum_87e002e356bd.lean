-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_clm_apply_eq_sum_87e002e356bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:42.987272+00:00
-- url     : https://prove2.me/submissions/967a2194-efb9-4e43-8a7f-7b69a3f2f5fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitivePresentationCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (lam : (σ → ℂ) →L[ℂ] ℂ) (x : σ → ℂ) :
    lam x = ∑ m, x m * lam (fun j => if m = j then 1 else 0) := by
  have := LinearMap.pi_apply_eq_sum_univ (lam : (σ → ℂ) →ₗ[ℂ] ℂ) x
  simpa [smul_eq_mul] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

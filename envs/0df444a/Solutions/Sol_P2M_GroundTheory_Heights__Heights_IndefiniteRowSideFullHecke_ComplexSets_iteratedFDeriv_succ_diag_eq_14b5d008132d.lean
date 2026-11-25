-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_iteratedFDeriv_succ_diag_eq_14b5d008132d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:18.345974+00:00
-- url     : https://prove2.me/submissions/5a07ec2e-8590-40ca-94c3-12ef56db53b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense

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
open Topology Filter Module
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀) (n : ℕ) (v : E) :
    iteratedFDeriv ℂ (n + 1) ψ y₀ (fun _ => v) =
      iteratedFDeriv ℂ n (fun y => fderiv ℂ ψ y v) y₀ (fun _ => v) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hc : ContDiffAt ℂ ω (fderiv ℂ ψ) y₀ := hψ.fderiv.contDiffAt
  have h1 := (ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left hc (i := n) le_top
  have h2 : (fun y => fderiv ℂ ψ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ ψ := rfl
  rw [h2, h1]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

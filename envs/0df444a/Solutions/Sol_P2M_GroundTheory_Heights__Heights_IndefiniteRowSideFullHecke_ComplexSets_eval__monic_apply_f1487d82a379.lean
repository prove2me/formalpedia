-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval__monic_apply_f1487d82a379
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:31:59.619506+00:00
-- url     : https://prove2.me/submissions/744edca9-6a20-46b4-aae7-0aef5785eeb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPrimitiveForm

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
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (X ^ M + ∑ j, C (b j) * X ^ (j : ℕ)) z =
      g z ^ M + ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by
  simp [eval₂_finsetSum, Finset.sum_apply, preLinear]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

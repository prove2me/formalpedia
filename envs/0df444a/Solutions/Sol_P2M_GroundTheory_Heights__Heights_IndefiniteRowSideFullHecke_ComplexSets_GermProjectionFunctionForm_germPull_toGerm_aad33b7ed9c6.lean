-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermProjectionFunctionForm_germPull_toGerm_aad33b7ed9c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:55.790365+00:00
-- url     : https://prove2.me/submissions/476164a4-374a-4d60-a7d0-f6d3cb3d44e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermProjectionFunctionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermProjectionFunctionForm

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
open Topology Filter PrimeGermPrimitivePresentation
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm
theorem _root_.solution {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u : anFun (A w)) :
    germPull A (A.analyticAt w) rfl (toGerm (A w) u) = toGerm w (compA A w u) :=
  Subtype.ext (germPull_coe A (A.analyticAt w) rfl _ u.1 rfl)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermProjectionFunctionForm

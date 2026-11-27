-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegularInjectivePieces_hypotheses_inhabited_f838a78e4164
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:17.19353+00:00
-- url     : https://prove2.me/submissions/f83e22e7-28a9-4664-9648-51b6273ee221

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularInjectivePieces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RegularInjectivePieces
theorem _root_.solution :
    IsOpen (Set.univ : Set (Fin 1 → ℂ)) ∧
      DifferentiableOn ℂ (fun w : Fin 1 → ℂ => fun _ : Fin 1 => w 0 ^ 2) Set.univ := by
  refine ⟨isOpen_univ, ?_⟩
  intro w _
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.2
  intro _
  exact ((differentiableAt_apply 0 w).pow 2)
end RegularInjectivePieces
end GroundTheory.Heights₂.Heights

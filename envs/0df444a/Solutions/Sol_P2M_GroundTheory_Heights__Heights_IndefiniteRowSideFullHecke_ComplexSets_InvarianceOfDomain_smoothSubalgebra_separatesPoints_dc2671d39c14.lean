-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_smoothSubalgebra_separatesPoints_dc2671d39c14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:57.448797+00:00
-- url     : https://prove2.me/submissions/1da6cd31-9bd3-4853-872b-3fcd28cccc4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
theorem _root_.solution : (smoothSubalgebra n).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨fun z => z i, ⟨⟨fun z => z i, continuous_apply i⟩, ?_, rfl⟩, hi⟩
  show ContDiff ℝ 1 fun z : Fin n → ℝ => z i
  exact contDiff_apply ℝ ℝ i
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain

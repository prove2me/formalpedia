-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:53.709225+00:00
-- url     : https://prove2.me/submissions/aa0433ec-8696-4aa1-a085-f7d421d99b7a

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
omit [AddCommGroup V]
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : SB (0 : V → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
end PositivityTheory.PlacePermOperatorBicommutantSpan

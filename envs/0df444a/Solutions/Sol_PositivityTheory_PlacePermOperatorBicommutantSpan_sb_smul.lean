-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:52.722321+00:00
-- url     : https://prove2.me/submissions/d906f7e3-79a9-4293-bf32-6358c0b1d0d9

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_mul

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
theorem _root_.solution (c : ℂ) {g : V → ℂ} (hg : SB g) : SB (c • g) := sb_mul (IsLocallyConstant.const c) hg
end PositivityTheory.PlacePermOperatorBicommutantSpan

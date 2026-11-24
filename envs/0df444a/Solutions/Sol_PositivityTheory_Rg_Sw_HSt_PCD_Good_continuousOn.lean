-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.Good.continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:54.937171+00:00
-- url     : https://prove2.me/submissions/f3f5e677-8599-4ad2-9d76-99893727db48

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
namespace PositivityTheory.Rg.Sw.HSt.PCD
namespace Good
theorem _root_.solution (hK : Good Ω K) : ContinuousOn (fun p : F × X => K p.1 p.2) (Ω ×ˢ univ) := by
  have h := (continuousMultilinearCurryFin0 ℝ F E).continuous.comp_continuousOn (hK.cont 0)
  refine h.congr fun p _ => ?_
  simp
end Good
end PositivityTheory.Rg.Sw.HSt.PCD

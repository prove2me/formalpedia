-- Prove2me | solution 1 for PositivityTheory.ThKF.L2.emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:48.700326+00:00
-- url     : https://prove2.me/submissions/0e486b87-f387-42f4-b7e5-57169ae4f601

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.L2
open MeasureTheory
open scoped ComplexConjugate Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
namespace PositivityTheory.ThKF.L2
theorem _root_.solution (g : G) : MeasurableEmbedding fun x : G => x * g := (Homeomorph.mulRight g).measurableEmbedding
end PositivityTheory.ThKF.L2

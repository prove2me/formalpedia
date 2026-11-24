-- Prove2me | solution 1 for PositivityTheory.ThKF.L2.fd_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:58.972748+00:00
-- url     : https://prove2.me/submissions/e0dc2311-eeca-429c-8e3b-17ee537466ab

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
theorem _root_.solution (h : IsFundamentalDomain Γ 𝓕 μ) (g : G) : IsFundamentalDomain Γ ((fun x => x * g) '' 𝓕) μ := by
  have := h.smul_of_comm (MulOpposite.op g)
  simpa [← Set.image_smul] using this
end PositivityTheory.ThKF.L2

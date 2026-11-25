-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_tsupport_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:38.262091+00:00
-- url     : https://prove2.me/submissions/713d47d3-6e6e-433e-af2d-d3e1d0c3cfe0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M E : Type*} [TopologicalSpace M] [Zero E] (f : M → E) (T : Set M)
    (hT : IsClosed T) (h : ∀ x, x ∉ T → f x = 0) : tsupport f ⊆ T := by
  refine closure_minimal (fun x hx => ?_) hT
  by_contra hxT
  exact hx (h x hxT)
end ReciprocityTheory.L2DbarEstimates.F

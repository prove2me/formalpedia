-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.leviZ_coord_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:21.52762+00:00
-- url     : https://prove2.me/submissions/b01ee1be-bdc0-4aae-8cbf-b6cbae4d6a5d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LeviZCoordChart

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (l : Fin n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    EqOn ((fun y => z y l) ∘ e.symm) (fun w : V n => w l) e.target := by
  intro w hw
  simp only [Function.comp_apply]
  rw [he (e.map_target hw), e.right_inv hw]
end ReciprocityTheory.L2DbarEstimates.F

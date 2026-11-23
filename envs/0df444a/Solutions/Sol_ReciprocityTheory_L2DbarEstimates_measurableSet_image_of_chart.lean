-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.measurableSet_image_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:48.805802+00:00
-- url     : https://prove2.me/submissions/bdab391e-9bd9-4145-a154-0a8aa67c1642

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (z : M → V n) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (S : Set M) (hS : MeasurableSet S) (hSe : S ⊆ e.source) :
    MeasurableSet (z '' S) := by
  have h1 : z '' S = e '' S := Set.image_congr (fun x hx => he (hSe hx))
  have h2 : e '' S = e.target ∩ e.symm ⁻¹' S := by
    have h3 := e.image_source_inter_eq' S
    rwa [Set.inter_eq_right.mpr hSe] at h3
  rw [h1, h2]
  have hm : MeasurableSet ((e.target).restrict e.symm ⁻¹' S) :=
    (e.continuousOn_symm.restrict).measurable hS
  have h4 := e.open_target.measurableSet.subtype_image hm
  convert h4 using 1
  ext w
  simp [Set.restrict, and_comm]
end ReciprocityTheory.L2DbarEstimates

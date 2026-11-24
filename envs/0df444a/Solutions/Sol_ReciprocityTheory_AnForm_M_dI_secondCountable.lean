-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:51.294458+00:00
-- url     : https://prove2.me/submissions/1fd611c5-a014-40a4-9016-081d5136afd6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) : SecondCountableTopology X := by
  have hU : ∀ k, SecondCountableTopology ((A.chart k).source) := fun k =>
    (A.chart k).toHomeomorphSourceTarget.secondCountableTopology
  have hcov : ⋃ k, (A.chart k).source = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (A.cover x)
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun k => (A.chart k).open_source) hcov
end ReciprocityTheory.AnForm.M

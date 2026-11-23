-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_smooth_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:36.0989+00:00
-- url     : https://prove2.me/submissions/360174b4-ff30-44ab-92a9-680f9c3bdfe8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA

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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ m, A.Smooth (f m)) : A.Smooth (fun x => ∑ m ∈ s, f m x) := fun j => ContDiffOn.sum fun m _ => hf m j
end ReciprocityTheory.AnForm.M

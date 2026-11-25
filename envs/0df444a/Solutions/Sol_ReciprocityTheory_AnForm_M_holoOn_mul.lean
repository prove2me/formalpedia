-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holoOn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:25.838141+00:00
-- url     : https://prove2.me/submissions/788b79c4-884d-42e5-a986-e1e3dc845e74

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential

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
theorem _root_.solution (A : FinHolAtlas e X) {W : Set X} {G : X → ℂ} (h : A.HoloOn W G) (c : ℂ) :
    A.HoloOn W (fun z => c * G z) := fun j w hw => analyticAt_const.mul (h j w hw)
end ReciprocityTheory.AnForm.M

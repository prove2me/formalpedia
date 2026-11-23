-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.smoothOnAlg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:33.558884+00:00
-- url     : https://prove2.me/submissions/b2a5e692-504c-43f5-a4c0-0b117eb7b8b1

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
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : SmoothOnAlgStatement := by
  intro e X _ A U V f g c hf hg hVU
  refine ⟨fun j => ?_, fun j => ?_⟩
  · exact ((hf j).mono fun y hy => ⟨hy.1, hVU hy.2⟩).add (hg j)
  · exact contDiffOn_const.mul (hf j)
end ReciprocityTheory.AnForm.M

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holoOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:37.256992+00:00
-- url     : https://prove2.me/submissions/4be83092-6955-425e-8bb9-c5c7f64f5793

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {U V : Set (OnePoint ℂ)} {g : OnePoint ℂ → ℂ} (h : p1.HoloOn U g)
    (hVU : V ⊆ U) : p1.HoloOn V g := by
  intro j w hw
  exact h j w ⟨hw.1, hVU hw.2⟩
end ReciprocityTheory.AnForm.M

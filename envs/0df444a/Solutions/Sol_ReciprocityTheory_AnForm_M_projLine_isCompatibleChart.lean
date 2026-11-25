-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_isCompatibleChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:15.722984+00:00
-- url     : https://prove2.me/submissions/4e00baf2-51a6-45df-b345-51dd94c46522

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
theorem _root_.solution (k : Fin 2) : IsCompatChart p1 (p1.chart k) := by
  intro j
  exact ⟨p1.holo j k, p1.holo k j⟩
end ReciprocityTheory.AnForm.M

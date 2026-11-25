-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntegrableCont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:11.415637+00:00
-- url     : https://prove2.me/submissions/37d93672-464b-481a-b8ba-b9c36c53acba

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : MIntegrableContStatement := by
  intro e X _ A Φ hΦ g hg j K hKt hK
  exact (((hg.comp_continuousOn (A.chart j).continuousOn_symm).mul
    (locDensCont A Φ hΦ j)).mono hKt).integrableOn_compact hK
end ReciprocityTheory.AnForm.M

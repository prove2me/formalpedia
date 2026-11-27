-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDensNonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:45.337536+00:00
-- url     : https://prove2.me/submissions/f47412aa-14ae-49c7-9d6b-0c526bd254ef

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasure
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_nonneg_of_psh


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
theorem _root_.solution : LocDensNonnegStatement := by
  intro e X _ A Φ hΦ hPsh j y hy
  exact locDens_nonneg_of_psh A Φ hΦ hPsh j hy
end ReciprocityTheory.AnForm.M

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:05.121583+00:00
-- url     : https://prove2.me/submissions/a7af6276-046a-40bf-9746-75079eac1853

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Theorems.Thm_ReciprocityTheory_AnForm_M_integralWithIndep

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
theorem _root_.solution : MIntEqStatement := by
  intro e X _ _ _ A P Φ hΦ g hg
  have h : Nonempty (ChartPartition A) := ⟨P⟩
  unfold mInt
  rw [dif_pos h]
  exact integralWithIndep A h.some P Φ hΦ g hg
end ReciprocityTheory.AnForm.M

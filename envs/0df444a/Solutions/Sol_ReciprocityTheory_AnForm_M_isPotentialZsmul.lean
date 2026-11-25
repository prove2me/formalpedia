-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPotentialZsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:26.047922+00:00
-- url     : https://prove2.me/submissions/6dcecd5e-9350-4f7c-9e9a-c93ae5b1bd04

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_mul

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
theorem _root_.solution : IsPotentialZsmulStatement := by
  intro e X _ A m P hP
  exact isPotential_mul A P hP (m : ℝ) (P.zsmul m) rfl (fun _ _ => rfl)
end ReciprocityTheory.AnForm.M

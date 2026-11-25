-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntRsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:27.118871+00:00
-- url     : https://prove2.me/submissions/e514978c-9e9c-4cf2-bf18-41f444231192

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons_rsmul

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
open scoped ContDiff ComplexOrder
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : MIntRsmulStatement := by
  intro e X _ A c P Φ hP hΦ g
  unfold mInt integralWith
  split_ifs with h
  · simp only [locDens_cons_rsmul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · simp
end ReciprocityTheory.AnForm.M

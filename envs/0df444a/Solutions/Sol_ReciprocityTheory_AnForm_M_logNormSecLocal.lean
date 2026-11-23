-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.logNormSecLocal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:25.86588+00:00
-- url     : https://prove2.me/submissions/22598015-ba75-451f-a52f-8449519f2541

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt

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
theorem _root_.solution : LogNormSecLocalStatement := by
  intro e X _ A L s x y hS hy hs
  unfold logNormSec
  rw [hS.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.mpr hs) (Real.exp_pos _).ne',
    Real.log_exp]
  ring
end ReciprocityTheory.AnForm.M

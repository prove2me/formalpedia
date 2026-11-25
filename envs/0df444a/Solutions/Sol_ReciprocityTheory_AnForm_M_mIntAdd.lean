-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:24.988225+00:00
-- url     : https://prove2.me/submissions/03b2b551-71ee-4e74-a041-8a48e0842056

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons_add
import Theorems.Thm_ReciprocityTheory_AnForm_M_integrableOn_weight

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
theorem _root_.solution : MIntAddStatement := by
  intro e X _ _ _ A P Q Φ hP hQ hΦ g hgP hgQ
  unfold mInt integralWith
  split_ifs with h
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some (Fin.cons P Φ) g hgP j
    have i2 := integrableOn_weight A h.some (Fin.cons Q Φ) g hgQ j
    rw [← integral_add i1 i2]
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    show _ = _ + _
    rw [locDens_cons_add A P Q Φ hP hQ j hy]
    ring
  · simp
end ReciprocityTheory.AnForm.M

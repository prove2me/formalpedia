-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurePreserving_tmUpd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:44.061388+00:00
-- url     : https://prove2.me/submissions/9ba449b8-c576-4eef-b8d5-971aaecfa596

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_tmUpd
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmUpd_preimage_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (i : ι) :
    MeasurePreserving (tmUpd i) ((torusProb ι).prod unitIntervalMeasure) (torusProb ι) := by
  refine ⟨measurable_tmUpd i, ?_⟩
  have h1 : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1 := by simp
  unfold torusProb
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_tmUpd i) (MeasurableSet.univ_pi hs), tmUpd_preimage_pi,
    Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  have hp : ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (update s i Set.univ j) =
      ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (s j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hp, Function.update_self, h1, one_mul, mul_comm]
end ReciprocityTheory.MultiplicativeHeights

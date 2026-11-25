-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_sum_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:55.696992+00:00
-- url     : https://prove2.me/submissions/5ea3a7f6-cfa9-46b7-816e-c54315b2bb2b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter

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
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {ι : Type*} [Fintype ι] {F : Set X} (hF : F.Finite) (h : ι → X → ℝ) :
    ∑ i, ∑ᶠ x ∈ F, h i x = ∑ᶠ x ∈ F, ∑ i, h i x := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hF]
  exact Finset.sum_comm
end ReciprocityTheory.AnForm.M

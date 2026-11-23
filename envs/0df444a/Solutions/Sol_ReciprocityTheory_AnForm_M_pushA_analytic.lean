-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:59.249667+00:00
-- url     : https://prove2.me/submissions/c40a6aa6-6133-429b-b01d-c766822d25d5

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
theorem _root_.solution (A : FinHolAtlas e X) {Q : Set X} {q : X → Fin e → ℂ}
    (hq : ∀ i, A.HoloOn Q (fun x => q x i)) (j : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart j).target) (hzQ : (A.chart j).symm z ∈ Q) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) z := by
  have := (analyticAt_pi_iff (f := fun i => (fun x => q x i) ∘ (A.chart j).symm) (e := z)).2
    (fun i => hq i j z ⟨hz, hzQ⟩)
  exact this
end ReciprocityTheory.AnForm.M

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_hasSum_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:11.429336+00:00
-- url     : https://prove2.me/submissions/84c3bfca-024a-44a7-bcd1-03186628927b

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
theorem _root_.solution (E : ℕ → Set X) (hE : Pairwise (Function.onFun Disjoint E)) (f : X → ℝ)
    (x : X) : HasSum (fun m => (E m).indicator f x) ((⋃ m, E m).indicator f x) := by
  by_cases hx : ∃ m0, x ∈ E m0
  · obtain ⟨m0, hm0⟩ := hx
    have hne : ∀ m, m ≠ m0 → (E m).indicator f x = 0 := by
      intro m hm
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.1 (hE hm) h hm0) f
    rw [Set.indicator_of_mem (Set.mem_iUnion.2 ⟨m0, hm0⟩), ← Set.indicator_of_mem hm0 f]
    exact hasSum_single m0 hne
  · push Not at hx
    rw [Set.indicator_of_notMem (by simpa using hx)]
    have : (fun m => (E m).indicator f x) = fun _ => 0 :=
      funext fun m => Set.indicator_of_notMem (hx m) f
    rw [this]
    exact hasSum_zero
end ReciprocityTheory.AnForm.M

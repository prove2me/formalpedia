-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_fib
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:00.072506+00:00
-- url     : https://prove2.me/submissions/5b24ae2f-e93a-4c9c-a471-129f7d7e174c

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
theorem _root_.solution (q : X → Fin e → ℂ) (s : (Fin e → ℂ) → X) {D : Set (Fin e → ℂ)}
    (hinj : Set.InjOn (q ∘ s) D) :
    (∀ z ∈ D, q ⁻¹' {q (s z)} ∩ s '' D = {s z}) ∧
      ∀ y, y ∉ (q ∘ s) '' D → q ⁻¹' {y} ∩ s '' D = ∅ := by
  refine ⟨fun z hz => ?_, fun y hy => ?_⟩
  · ext x
    constructor
    · rintro ⟨hx1, z', hz', rfl⟩
      have h : (q ∘ s) z' = (q ∘ s) z := hx1
      rw [hinj hz' hz h]
      rfl
    · rintro rfl
      exact ⟨rfl, z, hz, rfl⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    rintro hx1 z' hz' rfl
    exact hy ⟨z', hz', hx1⟩
end ReciprocityTheory.AnForm.M

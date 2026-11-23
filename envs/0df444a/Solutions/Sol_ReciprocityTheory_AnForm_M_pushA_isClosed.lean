-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:46.529726+00:00
-- url     : https://prove2.me/submissions/615c07c6-1bbb-410f-8016-46ac6c08c904

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
theorem _root_.solution (A : FinHolAtlas e X) {S : Set X} (hS : A.IsAnalyticSubset S) :
    IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hS x
  have hx' : x ∉ {y ∈ W | ∀ i, f i y = 0} := by
    rw [← hSW]; exact fun h => hx h.1
  have hex : ∃ i, f i x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx' ⟨hxW, h⟩
  obtain ⟨i, hi⟩ := hex
  obtain ⟨k, hk⟩ := A.cover x
  have hcont : ContinuousAt (f i) x := by
    have han : AnalyticAt ℂ (f i ∘ (A.chart k).symm) (A.chart k x) :=
      hf i k _ ⟨(A.chart k).map_source hk, by simpa [(A.chart k).left_inv hk] using hxW⟩
    have h1 : ContinuousAt ((f i ∘ (A.chart k).symm) ∘ (A.chart k)) x :=
      ContinuousAt.comp (g := f i ∘ (A.chart k).symm) han.continuousAt
        ((A.chart k).continuousAt hk)
    refine h1.congr ?_
    filter_upwards [(A.chart k).open_source.mem_nhds hk] with y hy
    simp [(A.chart k).left_inv hy]
  have hN : {y | f i y ≠ 0} ∈ 𝓝 x := hcont.eventually_ne hi
  obtain ⟨N, hNsub, hNo, hxN⟩ := mem_nhds_iff.1 (inter_mem hN (hWo.mem_nhds hxW))
  refine ⟨N, fun y hy hyS => ?_, hNo, hxN⟩
  have : y ∈ S ∩ W := ⟨hyS, (hNsub hy).2⟩
  rw [hSW] at this
  exact (hNsub hy).1 (this.2 i)
end ReciprocityTheory.AnForm.M

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:24.562332+00:00
-- url     : https://prove2.me/submissions/8eb9943b-e82a-444f-bed9-8d141cd841e7

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
theorem _root_.solution (O : Set (Fin e → ℂ)) (hO : IsOpen O) (τ : (Fin e → ℂ) → (Fin e → ℂ))
    (hloc : ∀ z ∈ O, ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ Set.InjOn τ W) :
    ∃ D : ℕ → Set (Fin e → ℂ), (∀ m, MeasurableSet (D m)) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ m, D m) = O ∧ ∀ m, Set.InjOn τ (D m) := by
  set 𝒮 : Set (Set (Fin e → ℂ)) := {W | IsOpen W ∧ W ⊆ O ∧ Set.InjOn τ W}
  obtain ⟨T, hTc, hTS, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable 𝒮 (fun W hW => hW.1)
  have hU : ⋃₀ 𝒮 ⊆ O := fun z ⟨W, hW, hz⟩ => hW.2.1 hz
  have hU' : O ⊆ ⋃₀ 𝒮 := by
    intro z hz
    obtain ⟨W, hWo, hzW, hinj⟩ := hloc z hz
    exact ⟨W ∩ O, ⟨hWo.inter hO, Set.inter_subset_right, hinj.mono Set.inter_subset_left⟩,
      ⟨hzW, hz⟩⟩
  have hUeq : ⋃₀ T = O := hTU.trans (subset_antisymm hU hU')
  have hT'c : (insert (∅ : Set (Fin e → ℂ)) T).Countable := hTc.insert ∅
  obtain ⟨f, hf⟩ := hT'c.exists_eq_range (Set.insert_nonempty _ _)
  have hfS : ∀ m, f m ∈ 𝒮 := by
    intro m
    have hm : f m ∈ insert (∅ : Set (Fin e → ℂ)) T := by rw [hf]; exact Set.mem_range_self m
    rcases hm with h | h
    · rw [h]; exact ⟨isOpen_empty, Set.empty_subset _, Set.injOn_empty _⟩
    · exact hTS h
  refine ⟨disjointed f, fun m => MeasurableSet.disjointed (fun i => (hfS i).1.measurableSet) m,
    disjoint_disjointed f, ?_, fun m => (hfS m).2.2.mono (disjointed_subset f m)⟩
  rw [iUnion_disjointed, ← Set.sUnion_range, ← hf, Set.sUnion_insert, Set.empty_union, hUeq]
end ReciprocityTheory.AnForm.M

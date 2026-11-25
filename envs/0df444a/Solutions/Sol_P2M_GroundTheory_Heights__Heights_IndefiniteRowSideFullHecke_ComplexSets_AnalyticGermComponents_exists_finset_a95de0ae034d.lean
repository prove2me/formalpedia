-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_exists_finset_a95de0ae034d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:25.994109+00:00
-- url     : https://prove2.me/submissions/e1f4013e-d1bf-48db-8c2b-f77d9f69481a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_isAnalyticNear_inter_zero_4847adeb363d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_apply_eq_zero_of_not_c3046b8ba998
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_vanishingIdeal_lt_54d5d5c03d4d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
theorem _root_.solution {w : σ → ℂ} (hN : IsNoetherianRing (holGerms w)) (X : Set (σ → ℂ))
    (hX : IsAnalyticNear X w) (hw : w ∈ X) :
    ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W := by
  classical
  suffices H : ∀ J : Ideal (holGerms w), ∀ X : Set (σ → ℂ), vanishingIdeal X w = J → IsAnalyticNear X w →
      w ∈ X → ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
        ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W from H _ X rfl hX hw
  intro J
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro X hJ hX hw
  by_cases hirr : GermIrreducibleAt X w
  · refine ⟨{X}, ?_, Set.univ, Filter.univ_mem, ?_⟩
    · intro Y hY
      rw [Finset.mem_singleton] at hY
      exact hY ▸ ⟨hX, hirr⟩
    · simp
  obtain ⟨f, g, hf, hg, hfg, hnf, hng⟩ : ∃ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧
      (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) ∧ ¬ (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∧
      ¬ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) := by
    by_contra hcon
    refine hirr ⟨hw, fun f g hf hg hfg => ?_⟩
    by_contra h
    rw [not_or] at h
    exact hcon ⟨f, g, hf, hg, hfg, h.1, h.2⟩
  have hgf : ∀ᶠ z in 𝓝 w, z ∈ X → g z * f z = 0 := by
    filter_upwards [hfg] with z h hz
    rw [mul_comm]
    exact h hz
  have hfw : f w = 0 := apply_eq_zero_of_not hf hfg hng
  have hgw : g w = 0 := apply_eq_zero_of_not hg hgf hnf
  obtain ⟨s₁, hs₁, W₁, hW₁, hX₁⟩ := ih _ (hJ ▸ vanishingIdeal_lt hf hnf) _ rfl
    (isAnalyticNear_inter_zero hX hf) ⟨hw, hfw⟩
  obtain ⟨s₂, hs₂, W₂, hW₂, hX₂⟩ := ih _ (hJ ▸ vanishingIdeal_lt hg hng) _ rfl
    (isAnalyticNear_inter_zero hX hg) ⟨hw, hgw⟩
  refine ⟨s₁ ∪ s₂, ?_, W₁ ∩ W₂ ∩ {z | z ∈ X → f z * g z = 0}, inter_mem (inter_mem hW₁ hW₂) hfg, ?_⟩
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · exact hs₁ Y h
    · exact hs₂ Y h
  ext z
  have e₁ := Set.ext_iff.1 hX₁ z
  have e₂ := Set.ext_iff.1 hX₂ z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at e₁ e₂
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.mem_union]
  constructor
  · rintro ⟨hzX, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases mul_eq_zero.1 (hz0 hzX) with h | h
    · obtain ⟨Y, hY, hzY⟩ := (e₁.1 ⟨⟨hzX, h⟩, hz₁⟩).1
      exact ⟨Y, Or.inl hY, hzY⟩
    · obtain ⟨Y, hY, hzY⟩ := (e₂.1 ⟨⟨hzX, h⟩, hz₂⟩).1
      exact ⟨Y, Or.inr hY, hzY⟩
  · rintro ⟨⟨Y, hY, hzY⟩, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases hY with hY | hY
    · exact (e₁.2 ⟨⟨Y, hY, hzY⟩, hz₁⟩).1.1
    · exact (e₂.2 ⟨⟨Y, hY, hzY⟩, hz₂⟩).1.1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents

-- Prove2me | solution 1 for SourceTheory.EqualSources.reversed_implication
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:10:46.793797+00:00
-- url     : https://prove2.me/submissions/55f97e28-a296-4ceb-8ec0-cf73fb73acc5

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources.RevAux

open SourceTheory.Uniform MeasureTheory

lemma prob_mem_Icc {S : Type*} {𝒮 : Set (Set S)} {P : Set S → ℝ} (h𝒮 : IsSetAlgebra 𝒮)
    (hP : IsProbOn 𝒮 P) {E : Set S} (hE : E ∈ 𝒮) : P E ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h0, hadd⟩ := hP
  have hc := hadd E hE Eᶜ (h𝒮.compl_mem hE) disjoint_compl_right
  rw [union_compl_self, h1] at hc
  have := h0 Eᶜ (h𝒮.compl_mem hE)
  exact ⟨h0 E hE, by linarith⟩

lemma prob_compl {S : Type*} {𝒮 : Set (Set S)} {P : Set S → ℝ} (h𝒮 : IsSetAlgebra 𝒮)
    (hP : IsProbOn 𝒮 P) {E : Set S} (hE : E ∈ 𝒮) : P Eᶜ = 1 - P E := by
  obtain ⟨h1, h0, hadd⟩ := hP
  have hc := hadd E hE Eᶜ (h𝒮.compl_mem hE) disjoint_compl_right
  rw [union_compl_self, h1] at hc
  linarith

/-- With a common source function, equal weights mean equal a-neutral probabilities. -/
lemma W_eq_iff {S : Type*} {W : Set S → ℝ} {𝒜 𝒞 : Set (Set S)} {PA PC : Set S → ℝ} {w : ℝ → ℝ}
    (hA : IsSetAlgebra 𝒜) (hC : IsSetAlgebra 𝒞) (hPA : IsProbOn 𝒜 PA) (hPC : IsProbOn 𝒞 PC)
    (hwA : IsSourceFunction W 𝒜 PA w) (hwC : IsSourceFunction W 𝒞 PC w)
    {E F : Set S} (hE : E ∈ 𝒜) (hF : F ∈ 𝒞) : W E = W F ↔ PA E = PC F := by
  rw [hwA.2 E hE, hwC.2 F hF]
  exact hwA.1.1.2.1.injOn.eq_iff (prob_mem_Icc hA hPA hE) (prob_mem_Icc hC hPC hF)

lemma part_compl3 {S : Type*} {A₁ A₂ A₃ : Set S} (h12 : Disjoint A₁ A₂) (h13 : Disjoint A₁ A₃)
    (h23 : Disjoint A₂ A₃) (hU : A₁ ∪ A₂ ∪ A₃ = univ) : A₃ᶜ = A₁ ∪ A₂ := by
  ext s
  have hs : s ∈ A₁ ∪ A₂ ∪ A₃ := hU ▸ mem_univ s
  constructor
  · intro h; rcases hs with (h' | h') | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd h' h
  · rintro (h | h) h3
    · exact Set.disjoint_left.mp h13 h h3
    · exact Set.disjoint_left.mp h23 h h3

lemma part_compl2 {S : Type*} {A₁ A₂ A₃ : Set S} (h12 : Disjoint A₁ A₂) (h13 : Disjoint A₁ A₃)
    (h23 : Disjoint A₂ A₃) (hU : A₁ ∪ A₂ ∪ A₃ = univ) : A₂ᶜ = A₁ ∪ A₃ := by
  ext s
  have hs : s ∈ A₁ ∪ A₂ ∪ A₃ := hU ▸ mem_univ s
  constructor
  · intro h; rcases hs with (h' | h') | h'
    · exact Or.inl h'
    · exact absurd h' h
    · exact Or.inr h'
  · rintro (h | h) h2
    · exact Set.disjoint_left.mp h12 h h2
    · exact Set.disjoint_left.mp h23 h2 h

/-- Matching threefold partitions of sources with a common source function have matching
middle cells and matching complements of middle cells. -/
lemma middle_match {S : Type*} {W : Set S → ℝ} {𝒜 𝒞 : Set (Set S)} {PA PC : Set S → ℝ}
    {w : ℝ → ℝ}
    (hA : IsSetAlgebra 𝒜) (hC : IsSetAlgebra 𝒞) (hPA : IsProbOn 𝒜 PA) (hPC : IsProbOn 𝒞 PC)
    (hwA : IsSourceFunction W 𝒜 PA w) (hwC : IsSourceFunction W 𝒞 PC w)
    {C₁ C₂ C₃ A₁ A₂ A₃ : Set S} (hCp : IsPartition3 𝒞 C₁ C₂ C₃) (hAp : IsPartition3 𝒜 A₁ A₂ A₃)
    (h1 : W A₁ = W C₁) (h3 : W (A₃ᶜ) = W (C₃ᶜ)) : W A₂ = W C₂ ∧ W (A₂ᶜ) = W (C₂ᶜ) := by
  obtain ⟨hA1, hA2, hA3, a12, a13, a23, aU⟩ := hAp
  obtain ⟨hC1, hC2, hC3, c12, c13, c23, cU⟩ := hCp
  rw [W_eq_iff hA hC hPA hPC hwA hwC hA1 hC1] at h1
  rw [W_eq_iff hA hC hPA hPC hwA hwC (hA.compl_mem hA3) (hC.compl_mem hC3)] at h3
  rw [part_compl3 a12 a13 a23 aU, part_compl3 c12 c13 c23 cU, hPA.2.2 _ hA1 _ hA2 a12,
    hPC.2.2 _ hC1 _ hC2 c12] at h3
  have hm : PA A₂ = PC C₂ := by linarith
  refine ⟨(W_eq_iff hA hC hPA hPC hwA hwC hA2 hC2).2 hm, ?_⟩
  rw [W_eq_iff hA hC hPA hPC hwA hwC (hA.compl_mem hA2) (hC.compl_mem hC2),
    prob_compl hA hPA hA2, prob_compl hC hPC hC2, hm]

lemma insens_common {S : Type*} {W : Set S → ℝ} {𝒜 𝒞 : Set (Set S)} {PA PC : Set S → ℝ}
    {w : ℝ → ℝ}
    (hA : IsSetAlgebra 𝒜) (hC : IsSetAlgebra 𝒞) (hPA : IsProbOn 𝒜 PA) (hPC : IsProbOn 𝒞 PC)
    (hwA : IsSourceFunction W 𝒜 PA w) (hwC : IsSourceFunction W 𝒞 PC w) (B D : Set S) :
    IsMoreInsensitive W 𝒜 𝒞 B D := by
  intro C₁ C₂ C₃ A₁ A₂ A₃ hCp hAp
  refine ⟨fun h1 h3 _ => ?_, fun _ h1 h3 => ?_⟩
  · exact (middle_match hA hC hPA hPC hwA hwC hCp hAp h1 h3).1.symm.le
  · exact (middle_match hA hC hPA hPC hwA hwC hCp hAp h1 h3).2.le

lemma pref_common {S : Type*} {W : Set S → ℝ} {𝒜 𝒞 : Set (Set S)} {PA PC : Set S → ℝ}
    {w : ℝ → ℝ}
    (hA : IsSetAlgebra 𝒜) (hC : IsSetAlgebra 𝒞) (hPA : IsProbOn 𝒜 PA) (hPC : IsProbOn 𝒞 PC)
    (hwA : IsSourceFunction W 𝒜 PA w) (hwC : IsSourceFunction W 𝒞 PC w) :
    IsPreferredTo W 𝒞 𝒜 := by
  intro C₁ hC₁ A₁ hA₁ h
  rw [W_eq_iff hA hC hPA hPC hwA hwC hA₁ hC₁] at h
  refine le_of_eq ((W_eq_iff hA hC hPA hPC hwA hwC (hA.compl_mem hA₁) (hC.compl_mem hC₁)).2 ?_)
  rw [prob_compl hA hPA hA₁, prob_compl hC hPC hC₁, h]

lemma regular_full {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop}
    {U : Γ → ℝ} {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {𝒮 : Set (Set S)}
    (h𝒮 : IsSource 𝓔 W 𝒮) : IsRegularRegion W 𝒮 ∅ univ := by
  intro E hE _ _
  refine ⟨0, h1.W_mono _ (h𝒮.subset (hE 0)) ∅ h1.events.empty_mem (empty_subset _),
    h1.W_mono univ h1.events.univ_mem _ (h1.events.compl_mem (h𝒮.subset (hE 0)))
      (subset_univ _)⟩

end SourceTheory.EqualSources.RevAux

open SourceTheory.EqualSources.RevAux in
theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PA PC : Set S → ℝ) (w : ℝ → ℝ)
    (hA : SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA) (hC : SourceTheory.Uniform.IsUniformWith pref U 𝒞 PC)
    (hwA : SourceTheory.Uniform.IsSourceFunction W 𝒜 PA w) (hwC : SourceTheory.Uniform.IsSourceFunction W 𝒞 PC w) :
    ∃ B ∈ 𝓔, ∃ D ∈ 𝓔, SourceTheory.Uniform.IsRegularRegion W 𝒜 B D ∧ SourceTheory.Uniform.IsRegularRegion W 𝒞 B D ∧
      SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒜 ∧ SourceTheory.Uniform.IsPreferredTo W 𝒜 𝒞 ∧
      SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D ∧ SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 B D := by
  refine ⟨∅, h1.events.empty_mem, univ, h1.events.univ_mem, regular_full h1 h𝒜,
    regular_full h1 h𝒞,
    pref_common h𝒜.algebra h𝒞.algebra hA.1 hC.1 hwA hwC,
    pref_common h𝒞.algebra h𝒜.algebra hC.1 hA.1 hwC hwA,
    insens_common h𝒜.algebra h𝒞.algebra hA.1 hC.1 hwA hwC ∅ univ,
    insens_common h𝒞.algebra h𝒜.algebra hC.1 hA.1 hwC hwA ∅ univ⟩

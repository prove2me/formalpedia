-- Prove2me | solution 1 for SourceTheory.PrefMatch.theorem_2_matching_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:44:16.49462+00:00
-- url     : https://prove2.me/submissions/e1e2c3e9-cf99-4cd8-80fb-a8f5e53f708c

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option autoImplicit false

namespace SrcH
open Set SourceTheory.Uniform

section
variable {S : Type*} {𝒮 : Set (Set S)} {P : Set S → ℝ}

theorem prob_compl (hA : MeasureTheory.IsSetAlgebra 𝒮) (hP : IsProbOn 𝒮 P) {E : Set S}
    (hE : E ∈ 𝒮) : P Eᶜ = 1 - P E := by
  have h := hP.2.2 E hE (Eᶜ) (hA.compl_mem hE) disjoint_compl_right
  rw [union_compl_self, hP.1] at h
  linarith

theorem prob_mem (hA : MeasureTheory.IsSetAlgebra 𝒮) (hP : IsProbOn 𝒮 P) {E : Set S}
    (hE : E ∈ 𝒮) : 0 ≤ P E ∧ P E ≤ 1 := by
  refine ⟨hP.2.1 E hE, ?_⟩
  have := hP.2.1 (Eᶜ) (hA.compl_mem hE)
  rw [prob_compl hA hP hE] at this
  linarith

theorem prob_empty (hA : MeasureTheory.IsSetAlgebra 𝒮) (hP : IsProbOn 𝒮 P) : P ∅ = 0 := by
  have h := prob_compl hA hP (hA.univ_mem)
  rw [compl_univ, hP.1] at h
  linarith

theorem part3_compl3 (hA : MeasureTheory.IsSetAlgebra 𝒮) (hP : IsProbOn 𝒮 P) {A₁ A₂ A₃ : Set S}
    (h : IsPartition3 𝒮 A₁ A₂ A₃) : A₃ᶜ = A₁ ∪ A₂ := by
  obtain ⟨-, -, -, h12, h13, h23, hu⟩ := h
  ext x
  have hx : x ∈ A₁ ∪ A₂ ∪ A₃ := by rw [hu]; trivial
  simp only [mem_compl_iff, mem_union] at hx ⊢
  constructor
  · intro hn
    rcases hx with (h1 | h2) | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd h3 hn
  · intro h3 hx3
    rcases h3 with h1 | h2
    · exact (Set.disjoint_left.mp h13 h1) hx3
    · exact (Set.disjoint_left.mp h23 h2) hx3

theorem part3_compl2 (hA : MeasureTheory.IsSetAlgebra 𝒮) (hP : IsProbOn 𝒮 P) {A₁ A₂ A₃ : Set S}
    (h : IsPartition3 𝒮 A₁ A₂ A₃) : A₂ᶜ = A₁ ∪ A₃ := by
  obtain ⟨-, -, -, h12, h13, h23, hu⟩ := h
  ext x
  have hx : x ∈ A₁ ∪ A₂ ∪ A₃ := by rw [hu]; trivial
  simp only [mem_compl_iff, mem_union] at hx ⊢
  constructor
  · intro hn
    rcases hx with (h1 | h2) | h3
    · exact Or.inl h1
    · exact absurd h2 hn
    · exact Or.inr h3
  · intro h3 hx3
    rcases h3 with h1 | h3
    · exact (Set.disjoint_left.mp h12 h1) hx3
    · exact (Set.disjoint_left.mp h23 hx3) h3

theorem part3_P3 (hA : MeasureTheory.IsSetAlgebra 𝒮) (hP : IsProbOn 𝒮 P) {A₁ A₂ A₃ : Set S}
    (h : IsPartition3 𝒮 A₁ A₂ A₃) :
    P (A₃ᶜ) = P A₁ + P A₂ ∧ P (A₂ᶜ) = P A₁ + P A₃ ∧ P A₁ + P A₂ + P A₃ = 1 := by
  have hc3 := part3_compl3 hA hP h
  have hc2 := part3_compl2 hA hP h
  obtain ⟨h1, h2, h3, h12, h13, h23, hu⟩ := h
  have e3 : P (A₃ᶜ) = P A₁ + P A₂ := by rw [hc3]; exact hP.2.2 A₁ h1 A₂ h2 h12
  have e2 : P (A₂ᶜ) = P A₁ + P A₃ := by rw [hc2]; exact hP.2.2 A₁ h1 A₃ h3 h13
  refine ⟨e3, e2, ?_⟩
  have := prob_compl hA hP h3
  linarith

theorem W_le_iff {W : Set S → ℝ} {w : ℝ → ℝ} (hA : MeasureTheory.IsSetAlgebra 𝒮)
    (hP : IsProbOn 𝒮 P) (hw : IsSourceFunction W 𝒮 P w) {E F : Set S} (hE : E ∈ 𝒮) (hF : F ∈ 𝒮) :
    W E ≤ W F ↔ P E ≤ P F := by
  rw [hw.2 E hE, hw.2 F hF]
  have hE' := prob_mem hA hP hE
  have hF' := prob_mem hA hP hF
  exact hw.1.1.2.1.le_iff_le ⟨hE'.1, hE'.2⟩ ⟨hF'.1, hF'.2⟩

theorem W_lt_iff {W : Set S → ℝ} {w : ℝ → ℝ} (hA : MeasureTheory.IsSetAlgebra 𝒮)
    (hP : IsProbOn 𝒮 P) (hw : IsSourceFunction W 𝒮 P w) {E F : Set S} (hE : E ∈ 𝒮) (hF : F ∈ 𝒮) :
    W E < W F ↔ P E < P F := by
  rw [hw.2 E hE, hw.2 F hF]
  have hE' := prob_mem hA hP hE
  have hF' := prob_mem hA hP hF
  exact hw.1.1.2.1.lt_iff_lt ⟨hE'.1, hE'.2⟩ ⟨hF'.1, hF'.2⟩

theorem W_eq_iff {W : Set S → ℝ} {w : ℝ → ℝ} (hA : MeasureTheory.IsSetAlgebra 𝒮)
    (hP : IsProbOn 𝒮 P) (hw : IsSourceFunction W 𝒮 P w) {E F : Set S} (hE : E ∈ 𝒮) (hF : F ∈ 𝒮) :
    W E = W F ↔ P E = P F := by
  rw [le_antisymm_iff, le_antisymm_iff, W_le_iff hA hP hw hE hF, W_le_iff hA hP hw hF hE]

end

section
variable {S : Type*} {𝒜 𝒞 : Set (Set S)} {W : Set S → ℝ} {PA PC : Set S → ℝ} {wA wC φ : ℝ → ℝ}

/-- cross-source comparison: W A vs W C in terms of φ (PA A) and PC C -/
theorem cross_le_iff (hA : MeasureTheory.IsSetAlgebra 𝒜) (hC : MeasureTheory.IsSetAlgebra 𝒞)
    (hPA : IsProbOn 𝒜 PA) (hPC : IsProbOn 𝒞 PC) (hwA : IsSourceFunction W 𝒜 PA wA)
    (hwC : IsSourceFunction W 𝒞 PC wC) (hφ : IsTransformation φ)
    (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) {A C : Set S} (hAm : A ∈ 𝒜) (hCm : C ∈ 𝒞) :
    (W A ≤ W C ↔ φ (PA A) ≤ PC C) ∧ (W C ≤ W A ↔ PC C ≤ φ (PA A)) ∧
    (W A < W C ↔ φ (PA A) < PC C) ∧ (W C < W A ↔ PC C < φ (PA A)) ∧
    (W A = W C ↔ φ (PA A) = PC C) := by
  have hpa := prob_mem hA hPA hAm
  have hpc := prob_mem hC hPC hCm
  have hφm : φ (PA A) ∈ Icc (0 : ℝ) 1 := hφ.1.1 ⟨hpa.1, hpa.2⟩
  have hWA : W A = wC (φ (PA A)) := by rw [hwA.2 A hAm]; exact hφA _ ⟨hpa.1, hpa.2⟩
  have hWC : W C = wC (PC C) := hwC.2 C hCm
  have hs := hwC.1.1.2.1
  have hpc' : PC C ∈ Icc (0 : ℝ) 1 := ⟨hpc.1, hpc.2⟩
  rw [hWA, hWC]
  refine ⟨hs.le_iff_le hφm hpc', hs.le_iff_le hpc' hφm, hs.lt_iff_lt hφm hpc',
    hs.lt_iff_lt hpc' hφm, ?_⟩
  exact ⟨fun h => hs.injOn hφm hpc' h, fun h => by rw [h]⟩

end
theorem range_gen {S : Type*} {𝒜 : Set (Set S)} {W : Set S → ℝ} {PA : Set S → ℝ} {wA : ℝ → ℝ}
    (hal : MeasureTheory.IsSetAlgebra 𝒜) (hconv : IsConvexRanged 𝒜 W) (hP : IsProbOn 𝒜 PA)
    (hwA : IsSourceFunction W 𝒜 PA wA) : ∀ q ∈ Icc (0 : ℝ) 1, ∃ A ∈ 𝒜, PA A = q := by
  intro q hq
  have hw := hwA.1.1
  have hmono := hw.2.1
  have hmem : wA q ∈ Icc (0 : ℝ) 1 := hw.1 hq
  have hWe : W ∅ = 0 := by rw [hwA.2 ∅ hal.empty_mem, prob_empty hal hP]; exact hw.2.2.1
  have hWu : W univ = 1 := by rw [hwA.2 univ hal.univ_mem, hP.1]; exact hw.2.2.2
  obtain ⟨B, hB, -, -, hBW⟩ := hconv ∅ hal.empty_mem univ hal.univ_mem (empty_subset _)
    (wA q) (by rw [hWe]; exact hmem.1) (by rw [hWu]; exact hmem.2)
  refine ⟨B, hB, ?_⟩
  have hb := prob_mem hal hP hB
  have : wA (PA B) = wA q := by rw [← hwA.2 B hB]; exact hBW
  exact hmono.injOn ⟨hb.1, hb.2⟩ hq this

end SrcH

open Set SourceTheory.Uniform SrcH

theorem solution {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (φ : ℝ → ℝ) (hφ : IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) :
    ∀ C₁ ∈ 𝒞, ∀ A₁ ∈ 𝒜, W A₁ = W C₁ →
      φ (PA A₁) = PC C₁ ∧ (W (A₁ᶜ) ≤ W (C₁ᶜ) ↔ φ (PA (A₁ᶜ)) ≤ 1 - φ (1 - PA (A₁ᶜ))) := by
  intro C₁ hC A₁ hA hm
  obtain ⟨⟨hPC, -⟩, ⟨hPA, -⟩, hwC, hwA⟩ := h2
  have hal := h𝒜.algebra
  have hcl := h𝒞.algebra
  have cr := fun {A C : Set S} (hAm : A ∈ 𝒜) (hCm : C ∈ 𝒞) =>
    cross_le_iff hal hcl hPA hPC hwA hwC hφ hφA hAm hCm
  have e1 := (cr hA hC).2.2.2.2.mp hm
  refine ⟨e1, ?_⟩
  rw [(cr (hal.compl_mem hA) (hcl.compl_mem hC)).1, prob_compl hcl hPC hC,
    prob_compl hal hPA hA, sub_sub_cancel, e1]

-- Prove2me | solution 1 for SourceTheory.EqualSources.regularity_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:06:49.186978+00:00
-- url     : https://prove2.me/submissions/8418e536-55be-4edb-836a-ee0a08a8d27e

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option autoImplicit false
open Set SourceTheory.Uniform

namespace MMC

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

theorem prob_diff (hA : MeasureTheory.IsSetAlgebra 𝒮) (hP : IsProbOn 𝒮 P) {E F : Set S}
    (hE : E ∈ 𝒮) (hF : F ∈ 𝒮) (hEF : E ⊆ F) : P (F \ E) = P F - P E := by
  have h := hP.2.2 E hE (F \ E) (hA.sdiff_mem hF hE) (by
    rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx)
  rw [union_diff_cancel hEF] at h
  linarith

end

/-- the values of a source function lift: any prescribed probability between `P E` and `P F` is attained. -/
theorem ex_P {S : Type*} {𝓔 : Set (Set S)} {W : Set S → ℝ} {𝒮 : Set (Set S)}
    (h𝒮 : IsSource 𝓔 W 𝒮) {P : Set S → ℝ} {w : ℝ → ℝ} (hP : IsProbOn 𝒮 P)
    (hw : IsSourceFunction W 𝒮 P w) {E F : Set S} (hE : E ∈ 𝒮) (hF : F ∈ 𝒮) (hEF : E ⊆ F)
    {q : ℝ} (h1 : P E ≤ q) (h2 : q ≤ P F) :
    ∃ G ∈ 𝒮, E ⊆ G ∧ G ⊆ F ∧ P G = q := by
  obtain ⟨⟨⟨hmaps, hmono, -, -⟩, -⟩, hW⟩ := hw
  have hE01 := prob_mem h𝒮.algebra hP hE
  have hF01 := prob_mem h𝒮.algebra hP hF
  have hq : q ∈ Icc (0:ℝ) 1 := ⟨hE01.1.trans h1, h2.trans hF01.2⟩
  have hm : MonotoneOn w (Icc 0 1) := hmono.monotoneOn
  obtain ⟨G, hG, hEG, hGF, hWG⟩ := h𝒮.convexRanged E hE F hF hEF (w q)
    (by rw [hW E hE]; exact hm ⟨hE01.1, hE01.2⟩ hq h1)
    (by rw [hW F hF]; exact hm hq ⟨hF01.1, hF01.2⟩ h2)
  refine ⟨G, hG, hEG, hGF, ?_⟩
  rw [hW G hG] at hWG
  exact hmono.injOn (prob_mem h𝒮.algebra hP hG) hq hWG

theorem reg4 {S : Type*} {𝓔 : Set (Set S)} {W : Set S → ℝ} {𝒮 : Set (Set S)}
    (h𝒮 : IsSource 𝓔 W 𝒮) {P : Set S → ℝ} {w : ℝ → ℝ} (hP : IsProbOn 𝒮 P)
    (hw : IsSourceFunction W 𝒮 P w) {B D : Set S} (hreg : IsRegularRegion W 𝒮 B D) :
    W B ≤ w (1 / 4) ∧ w (3 / 4) ≤ W D := by
  have hA := h𝒮.algebra
  have hP0 : P ∅ = 0 := by
    have := prob_compl hA hP hA.univ_mem
    rw [compl_univ, hP.1] at this; linarith
  have hnn := hP.2.1
  obtain ⟨G1, hG1, -, -, hPG1⟩ := ex_P h𝒮 hP hw hA.empty_mem hA.univ_mem (empty_subset _)
    (q := 1 / 4) (by rw [hP0]; norm_num) (by rw [hP.1]; norm_num)
  obtain ⟨G2, hG2, hG12, -, hPG2⟩ := ex_P h𝒮 hP hw hG1 hA.univ_mem (subset_univ _)
    (q := 1 / 2) (by rw [hPG1]; norm_num) (by rw [hP.1]; norm_num)
  obtain ⟨G3, hG3, hG23, -, hPG3⟩ := ex_P h𝒮 hP hw hG2 hA.univ_mem (subset_univ _)
    (q := 3 / 4) (by rw [hPG2]; norm_num) (by rw [hP.1]; norm_num)
  let E : Fin 4 → Set S := ![G1, G2 \ G1, G3 \ G2, G3ᶜ]
  have hEmem : ∀ j, E j ∈ 𝒮 := by
    intro j; fin_cases j
    · exact hG1
    · exact hA.sdiff_mem hG2 hG1
    · exact hA.sdiff_mem hG3 hG2
    · exact hA.compl_mem hG3
  have hEP : ∀ j, P (E j) = 1 / 4 := by
    intro j; fin_cases j
    · exact hPG1
    · show P (G2 \ G1) = _
      rw [prob_diff hA hP hG1 hG2 hG12, hPG1, hPG2]; norm_num
    · show P (G3 \ G2) = _
      rw [prob_diff hA hP hG2 hG3 hG23, hPG2, hPG3]; norm_num
    · show P (G3ᶜ) = _
      rw [prob_compl hA hP hG3, hPG3]; norm_num
  have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    have h12 : ∀ x, x ∈ G1 → x ∈ G2 := fun x hx => hG12 hx
    have h23 : ∀ x, x ∈ G2 → x ∈ G3 := fun x hx => hG23 hx
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip <;>
      (rw [Set.disjoint_left]; intro x hx hx'; simp [E] at hx hx'; aesop)
  have hunion : (⋃ j, E j) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases a1 : x ∈ G1
    · exact ⟨0, a1⟩
    by_cases a2 : x ∈ G2
    · exact ⟨1, a2, a1⟩
    by_cases a3 : x ∈ G3
    · exact ⟨2, a3, a2⟩
    · exact ⟨3, a3⟩
  obtain ⟨j, hj1, hj2⟩ := hreg E hEmem hdisj hunion
  have hB : B ∈ 𝒮 ∨ True := Or.inr trivial
  refine ⟨?_, ?_⟩
  · calc W B ≤ W (E j) := hj1
      _ = w (1 / 4) := by rw [(hw.2 _ (hEmem j)), hEP j]
  · calc w (3 / 4) = W ((E j)ᶜ) := by
          rw [hw.2 _ (hA.compl_mem (hEmem j)), prob_compl hA hP (hEmem j), hEP j]; norm_num
      _ ≤ W D := hj2

end MMC

theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ)
    (𝒮 : Set (Set S)) (h𝒮 : SourceTheory.Uniform.IsSource 𝓔 W 𝒮) (P : Set S → ℝ) (w : ℝ → ℝ)
    (hP : SourceTheory.Uniform.IsUniformWith pref U 𝒮 P) (hw : SourceTheory.Uniform.IsSourceFunction W 𝒮 P w)
    (B D : Set S) (hB : B ∈ 𝒮) (hD : D ∈ 𝒮) (hreg : SourceTheory.Uniform.IsRegularRegion W 𝒮 B D) :
    P B ≤ 1 / 4 ∧ (3 / 4 : ℝ) ≤ P D := by
  obtain ⟨hb, hd⟩ := MMC.reg4 h𝒮 hP.1 hw hreg
  obtain ⟨⟨⟨hmaps, hmono, -, -⟩, -⟩, hW⟩ := hw
  have hB01 := MMC.prob_mem h𝒮.algebra hP.1 hB
  have hD01 := MMC.prob_mem h𝒮.algebra hP.1 hD
  rw [hW B hB] at hb
  rw [hW D hD] at hd
  constructor
  · by_contra h
    push_neg at h
    have := hmono ⟨by norm_num, by norm_num⟩ ⟨hB01.1, hB01.2⟩ h
    linarith
  · by_contra h
    push_neg at h
    have := hmono ⟨hD01.1, hD01.2⟩ ⟨by norm_num, by norm_num⟩ h
    linarith

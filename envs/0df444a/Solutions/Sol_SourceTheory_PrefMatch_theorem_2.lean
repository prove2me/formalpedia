-- Prove2me | solution 1 for SourceTheory.PrefMatch.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:36:39.90434+00:00
-- url     : https://prove2.me/submissions/bafd3bcf-06d6-4fe1-a78e-c4f46059dee5

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set SourceTheory.Uniform MeasureTheory

namespace SrcThyThm2Aux

/-- Probabilities of events of a source lie in `[0,1]`, and complements get `1 - P`. -/
theorem prob_facts {S : Type*} {𝒮 : Set (Set S)} {P : Set S → ℝ} (halg : IsSetAlgebra 𝒮)
    (hP : IsProbOn 𝒮 P) {E : Set S} (hE : E ∈ 𝒮) :
    P E ∈ Icc (0 : ℝ) 1 ∧ P Eᶜ = 1 - P E := by
  obtain ⟨h1, h0, hadd⟩ := hP
  have hc : Eᶜ ∈ 𝒮 := halg.compl_mem hE
  have hsum : P (E ∪ Eᶜ) = P E + P Eᶜ := hadd E hE Eᶜ hc disjoint_compl_right
  rw [union_compl_self, h1] at hsum
  have := h0 E hE
  have := h0 Eᶜ hc
  refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- Every probability in `[0,1]` is attained by an event of the source. -/
theorem hit {S : Type*} {𝒮 : Set (Set S)} {P : Set S → ℝ} {W : Set S → ℝ} {w : ℝ → ℝ}
    (halg : IsSetAlgebra 𝒮) (hcr : IsConvexRanged 𝒮 W) (hW0 : W ∅ = 0) (hW1 : W univ = 1)
    (hP : IsProbOn 𝒮 P) (hw : IsSourceFunction W 𝒮 P w) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ∃ E ∈ 𝒮, P E = p := by
  obtain ⟨⟨⟨hmaps, hmono, _, _⟩, _⟩, hWE⟩ := hw
  have hwp := hmaps hp
  obtain ⟨B, hB, -, -, hWB⟩ := hcr ∅ halg.empty_mem univ halg.univ_mem (empty_subset _) (w p)
    (by rw [hW0]; exact hwp.1) (by rw [hW1]; exact hwp.2)
  refine ⟨B, hB, ?_⟩
  rw [hWE B hB] at hWB
  exact hmono.injOn (prob_facts halg hP hB).1 hp hWB

end SrcThyThm2Aux

open SrcThyThm2Aux in
theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : Assumption2 pref U W 𝒞 𝒜 PC PA wC wA) :
    IsPreferredTo W 𝒞 𝒜 ↔
      ∃ φ : ℝ → ℝ, IsTransformation φ ∧ IsDisliked φ ∧ ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p) := by
  obtain ⟨⟨hPC, -⟩, ⟨hPA, -⟩, hwC, hwA⟩ := h2
  have hwC' := hwC
  have hwA' := hwA
  obtain ⟨⟨⟨wCmaps, wCmono, wC0, wC1⟩, wCcont⟩, hWC⟩ := hwC'
  obtain ⟨⟨⟨wAmaps, wAmono, wA0, wA1⟩, wAcont⟩, hWA⟩ := hwA'
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hIc : ∀ p ∈ Icc (0 : ℝ) 1, 1 - p ∈ Icc (0 : ℝ) 1 := fun p hp =>
    ⟨by linarith [hp.2], by linarith [hp.1]⟩
  constructor
  · intro hpref
    -- surjectivity of wC on [0,1]
    have hsurj : ∀ y ∈ Icc (0 : ℝ) 1, ∃ a ∈ Icc (0 : ℝ) 1, wC a = y := by
      intro y hy
      have := intermediate_value_Icc (zero_le_one' ℝ) wCcont
      rw [wC0, wC1] at this
      exact this hy
    set g := Function.invFunOn wC (Icc (0 : ℝ) 1) with hg
    have hgspec : ∀ y ∈ Icc (0 : ℝ) 1, g y ∈ Icc (0 : ℝ) 1 ∧ wC (g y) = y := fun y hy =>
      Function.invFunOn_pos (hsurj y hy)
    set φ : ℝ → ℝ := fun p => g (wA p) with hφ
    have hφI : ∀ p ∈ Icc (0 : ℝ) 1, φ p ∈ Icc (0 : ℝ) 1 := fun p hp => (hgspec _ (wAmaps hp)).1
    have hφeq : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p) := fun p hp =>
      ((hgspec _ (wAmaps hp)).2).symm
    have hφmono : StrictMonoOn φ (Icc (0 : ℝ) 1) := by
      intro p hp q hq hpq
      have h := wAmono hp hq hpq
      rw [hφeq p hp, hφeq q hq] at h
      by_contra hc
      push Not at hc
      have := wCmono.monotoneOn (hφI q hq) (hφI p hp) hc
      linarith
    have hφ0 : φ 0 = 0 := by
      apply wCmono.injOn (hφI 0 hI0) hI0
      rw [← hφeq 0 hI0, wA0, wC0]
    have hφ1 : φ 1 = 1 := by
      apply wCmono.injOn (hφI 1 hI1) hI1
      rw [← hφeq 1 hI1, wA1, wC1]
    have hφsurj : ∀ y ∈ Icc (0 : ℝ) 1, ∃ p ∈ Icc (0 : ℝ) 1, φ p = y := by
      intro y hy
      have hwy := wCmaps hy
      have := intermediate_value_Icc (zero_le_one' ℝ) wAcont
      rw [wA0, wA1] at this
      obtain ⟨p, hp, hpy⟩ := this hwy
      refine ⟨p, hp, ?_⟩
      apply wCmono.injOn (hφI p hp) hy
      rw [← hφeq p hp, hpy]
    have hφcont : ContinuousOn φ (Icc (0 : ℝ) 1) := by
      let F : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x => ⟨φ x, hφI x x.2⟩
      have hFm : Monotone F := fun x y hxy =>
        Subtype.mk_le_mk.mpr (hφmono.monotoneOn x.2 y.2 hxy)
      have hFs : Function.Surjective F := by
        intro y
        obtain ⟨p, hp, hpy⟩ := hφsurj y y.2
        exact ⟨⟨p, hp⟩, Subtype.ext hpy⟩
      have hFc : Continuous F := hFm.continuous_of_surjective hFs
      rw [continuousOn_iff_continuous_domRestrict]
      exact continuous_subtype_val.comp hFc
    refine ⟨φ, ⟨⟨fun p hp => hφI p hp, hφmono, hφ0, hφ1⟩, hφcont⟩, ?_, hφeq⟩
    -- dislike
    intro p hp
    obtain ⟨A, hA, hPAA⟩ := hit h𝒜.algebra h𝒜.convexRanged h1.W_empty h1.W_univ hPA hwA hp
    obtain ⟨C, hC, hPCC⟩ := hit h𝒞.algebra h𝒞.convexRanged h1.W_empty h1.W_univ hPC hwC
      (hφI p hp)
    have hWeq : W A = W C := by
      rw [hWA A hA, hWC C hC, hPAA, hPCC, hφeq p hp]
    have h := hpref C hC A hA hWeq
    rw [hWA _ (h𝒜.algebra.compl_mem hA), hWC _ (h𝒞.algebra.compl_mem hC),
      (prob_facts h𝒜.algebra hPA hA).2, (prob_facts h𝒞.algebra hPC hC).2, hPAA, hPCC,
      hφeq (1 - p) (hIc p hp)] at h
    have h' : φ (1 - p) ≤ 1 - φ p := by
      by_contra hc
      push Not at hc
      have := wCmono (hIc _ (hφI p hp)) (hφI _ (hIc p hp)) hc
      linarith
    linarith
  · rintro ⟨φ, ⟨⟨φmaps, -, -, -⟩, -⟩, hdis, hφeq⟩
    intro C₁ hC A₁ hA hWeq
    obtain ⟨hpA, hcA⟩ := prob_facts h𝒜.algebra hPA hA
    obtain ⟨hpC, hcC⟩ := prob_facts h𝒞.algebra hPC hC
    rw [hWA A₁ hA, hWC C₁ hC, hφeq _ hpA] at hWeq
    have hq : φ (PA A₁) = PC C₁ := wCmono.injOn (φmaps hpA) hpC hWeq
    rw [hWA _ (h𝒜.algebra.compl_mem hA), hWC _ (h𝒞.algebra.compl_mem hC), hcA, hcC,
      hφeq _ (hIc _ hpA)]
    have hd := hdis (1 - PA A₁) (hIc _ hpA)
    rw [sub_sub_cancel, hq] at hd
    have : φ (1 - PA A₁) ≤ 1 - PC C₁ := by linarith
    exact wCmono.monotoneOn (φmaps (hIc _ hpA)) (hIc _ hpC) this

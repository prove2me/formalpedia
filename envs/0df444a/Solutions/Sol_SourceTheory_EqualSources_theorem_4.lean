-- Prove2me | solution 1 for SourceTheory.EqualSources.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:15:09.616989+00:00
-- url     : https://prove2.me/submissions/3330eef4-4243-4de5-bd74-df4c83465f08

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model
import Theorems.Thm_SourceTheory_EqualSources_observation_3
import Theorems.Thm_SourceTheory_EqualSources_theorem_1
import Theorems.Thm_SourceTheory_EqualSources_reversed_implication
import Theorems.Thm_SourceTheory_EqualSources_pmatcher_symmetric
import Theorems.Thm_SourceTheory_EqualSources_subadditive_pmatcher
import Theorems.Thm_SourceTheory_EqualSources_subadditive_pmatcher_inv
import Theorems.Thm_SourceTheory_EqualSources_linear_on_half
import Theorems.Thm_SourceTheory_EqualSources_pmatcher_identity
import Theorems.Thm_SourceTheory_Uniform_source_function_exists

open Set

namespace SourceTheory.EqualSources.Thm4Aux

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

lemma W_eq_iff {S : Type*} {W : Set S → ℝ} {𝒜 𝒞 : Set (Set S)} {PA PC : Set S → ℝ} {w : ℝ → ℝ}
    (hA : IsSetAlgebra 𝒜) (hC : IsSetAlgebra 𝒞) (hPA : IsProbOn 𝒜 PA) (hPC : IsProbOn 𝒞 PC)
    (hwA : IsSourceFunction W 𝒜 PA w) (hwC : IsSourceFunction W 𝒞 PC w)
    {E F : Set S} (hE : E ∈ 𝒜) (hF : F ∈ 𝒞) : W E = W F ↔ PA E = PC F := by
  rw [hwA.2 E hE, hwC.2 F hF]
  exact hwA.1.1.2.1.injOn.eq_iff (prob_mem_Icc hA hPA hE) (prob_mem_Icc hC hPC hF)

lemma part_compl3 {S : Type*} {A₁ A₂ A₃ : Set S} (h13 : Disjoint A₁ A₃)
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
  rw [part_compl3 a13 a23 aU, part_compl3 c13 c23 cU, hPA.2.2 _ hA1 _ hA2 a12,
    hPC.2.2 _ hC1 _ hC2 c12] at h3
  have hm : PA A₂ = PC C₂ := by linarith
  refine ⟨(W_eq_iff hA hC hPA hPC hwA hwC hA2 hC2).2 hm, ?_⟩
  rw [W_eq_iff hA hC hPA hPC hwA hwC (hA.compl_mem hA2) (hC.compl_mem hC2),
    prob_compl hA hPA hA2, prob_compl hC hPC hC2, hm]

/-- With a common source function, `𝒜` is more insensitive than `𝒞` with any region. -/
lemma insens_common {S : Type*} {W : Set S → ℝ} {𝒜 𝒞 : Set (Set S)} {PA PC : Set S → ℝ}
    {w : ℝ → ℝ}
    (hA : IsSetAlgebra 𝒜) (hC : IsSetAlgebra 𝒞) (hPA : IsProbOn 𝒜 PA) (hPC : IsProbOn 𝒞 PC)
    (hwA : IsSourceFunction W 𝒜 PA w) (hwC : IsSourceFunction W 𝒞 PC w) (B D : Set S) :
    IsMoreInsensitive W 𝒜 𝒞 B D := by
  intro C₁ C₂ C₃ A₁ A₂ A₃ hCp hAp
  refine ⟨fun h1 h3 _ => ?_, fun _ h1 h3 => ?_⟩
  · exact (middle_match hA hC hPA hPC hwA hwC hCp hAp h1 h3).1.symm.le
  · exact (middle_match hA hC hPA hPC hwA hwC hCp hAp h1 h3).2.le

/-- A transformation (continuous probability weighting function) has an inverse transformation
on `[0, 1]`. -/
lemma inverse_transformation (w : ℝ → ℝ) (hw : IsTransformation w) :
    ∃ v : ℝ → ℝ, IsTransformation v ∧ ∀ p ∈ Icc (0 : ℝ) 1, v (w p) = p ∧ w (v p) = p := by
  obtain ⟨⟨hmaps, hmono, h0, h1⟩, hcont⟩ := hw
  let f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x => ⟨w x, hmaps x.2⟩
  have hf : StrictMono f := fun x y hxy => hmono x.2 y.2 hxy
  have hsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    have hq' : q ∈ Icc (w 0) (w 1) := by rw [h0, h1]; exact hq
    obtain ⟨p, hp, hpq⟩ := intermediate_value_Icc zero_le_one hcont hq'
    exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩
  let e := StrictMono.orderIsoOfSurjective f hf hsurj
  have he : ∀ x, (e x : ℝ) = w x := fun x => rfl
  let v : ℝ → ℝ := fun p => if h : p ∈ Icc (0 : ℝ) 1 then (e.symm ⟨p, h⟩ : ℝ) else p
  have hv : ∀ p (h : p ∈ Icc (0 : ℝ) 1), v p = (e.symm ⟨p, h⟩ : ℝ) := fun p h => dif_pos h
  have hvw : ∀ p ∈ Icc (0 : ℝ) 1, v (w p) = p := by
    intro p hp
    rw [hv _ (hmaps hp)]
    have : (⟨w p, hmaps hp⟩ : Icc (0 : ℝ) 1) = e ⟨p, hp⟩ := Subtype.ext (he ⟨p, hp⟩).symm
    rw [this, e.symm_apply_apply]
  have hwv : ∀ p ∈ Icc (0 : ℝ) 1, w (v p) = p := by
    intro p hp
    rw [hv _ hp, ← he, e.apply_symm_apply]
  refine ⟨v, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, fun p hp => ⟨hvw p hp, hwv p hp⟩⟩
  · intro p hp; rw [hv _ hp]; exact (e.symm ⟨p, hp⟩).2
  · intro p hp q hq hpq
    rw [hv _ hp, hv _ hq]
    exact e.symm.strictMono (show (⟨p, hp⟩ : Icc (0 : ℝ) 1) < ⟨q, hq⟩ from hpq)
  · have := hvw 0 ⟨le_rfl, zero_le_one⟩; rwa [h0] at this
  · have := hvw 1 ⟨zero_le_one, le_rfl⟩; rwa [h1] at this
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Icc (0 : ℝ) 1).domRestrict v = fun x => (e.symm x : ℝ) := by
      funext x; rw [Set.domRestrict_apply, hv _ x.2]
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous

lemma comp_transformation (v w : ℝ → ℝ) (hv : IsTransformation v) (hw : IsTransformation w) :
    IsTransformation (fun p => v (w p)) := by
  obtain ⟨⟨vmaps, vmono, v0, v1⟩, vcont⟩ := hv
  obtain ⟨⟨wmaps, wmono, w0, w1⟩, wcont⟩ := hw
  refine ⟨⟨vmaps.comp wmaps, vmono.comp wmono wmaps, ?_, ?_⟩, vcont.comp wcont wmaps⟩
  · simp [w0, v0]
  · simp [w1, v1]

end SourceTheory.EqualSources.Thm4Aux

open SourceTheory.EqualSources SourceTheory.EqualSources.Thm4Aux in
theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞) :
    ((∃ B ∈ 𝓔, ∃ D ∈ 𝓔, SourceTheory.Uniform.IsRegularRegion W 𝒜 B D ∧ SourceTheory.Uniform.IsRegularRegion W 𝒞 B D ∧
        SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒜 ∧ SourceTheory.Uniform.IsPreferredTo W 𝒜 𝒞 ∧
        SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D ∧ SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 B D) ↔
      ∃ (PA PC : Set S → ℝ) (w : ℝ → ℝ), SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA ∧ SourceTheory.Uniform.IsUniformWith pref U 𝒞 PC ∧
        SourceTheory.Uniform.IsSourceFunction W 𝒜 PA w ∧ SourceTheory.Uniform.IsSourceFunction W 𝒞 PC w) ∧
    ((∃ (PA PC : Set S → ℝ) (w : ℝ → ℝ), SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA ∧ SourceTheory.Uniform.IsUniformWith pref U 𝒞 PC ∧
        SourceTheory.Uniform.IsSourceFunction W 𝒜 PA w ∧ SourceTheory.Uniform.IsSourceFunction W 𝒞 PC w) →
      SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 ∅ univ ∧ SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 ∅ univ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨B, hB, D, hD, regA, regC, pCA, pAC, iAC, iCA⟩
    have obsA := observation_3 𝓔 pref U W h1 𝒜 𝒞 𝒜 h𝒜 h𝒞 h𝒜
    have obsC := observation_3 𝓔 pref U W h1 𝒞 𝒜 𝒞 h𝒞 h𝒜 h𝒞
    have pAA := obsA.1 pCA pAC
    have pCC := obsC.1 pAC pCA
    have iAA := obsA.2 B hB D hD B hB D hD iAC iCA B hB D hD le_rfl le_rfl le_rfl le_rfl
    have iCC := obsC.2 B hB D hD B hB D hD iCA iAC B hB D hD le_rfl le_rfl le_rfl le_rfl
    obtain ⟨PA, hPA⟩ := (theorem_1 𝓔 pref U W h1 𝒜 h𝒜).2 ⟨pAA, B, hB, D, hD, regA, iAA⟩
    obtain ⟨PC, hPC⟩ := (theorem_1 𝓔 pref U W h1 𝒞 h𝒞).2 ⟨pCC, B, hB, D, hD, regC, iCC⟩
    obtain ⟨wA, hwA⟩ :=
      SourceTheory.Uniform.source_function_exists 𝓔 pref U W h1 𝒜 h𝒜 PA hPA
    obtain ⟨wC, hwC⟩ :=
      SourceTheory.Uniform.source_function_exists 𝓔 pref U W h1 𝒞 h𝒞 PC hPC
    obtain ⟨vC, hvC, hvCinv⟩ := inverse_transformation wC hwC.1
    set φ : ℝ → ℝ := fun p => vC (wA p) with hφdef
    have hφ : SourceTheory.Uniform.IsTransformation φ := comp_transformation vC wA hvC hwA.1
    have hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p) := fun p hp =>
      ((hvCinv (wA p) (hwA.1.1.1 hp)).2).symm
    have h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA := ⟨hPC, hPA, hwC, hwA⟩
    obtain ⟨hsym, hhalf⟩ :=
      pmatcher_symmetric 𝓔 pref U W 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2 pCA pAC φ hφ hφA
    have hsub := subadditive_pmatcher 𝓔 pref U W 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2 B D hB hD regA iAC
      φ hφ hφA
    obtain ⟨ψ, -, hψ⟩ := inverse_transformation φ hφ
    have hψ' : ∀ p ∈ Icc (0 : ℝ) 1, ψ (φ p) = p ∧ φ (ψ p) = p := hψ
    have hsubψ := subadditive_pmatcher_inv 𝓔 pref U W 𝒜 𝒞 h𝒜 h𝒞 PC PA wC wA h2 B D hB hD regC
      iCA φ ψ hφ hφA hψ'
    obtain ⟨c, hlin⟩ := linear_on_half φ ψ hφ hψ' hhalf hsub hsubψ
    have hid := pmatcher_identity φ hφ c hlin hhalf hsym
    refine ⟨PA, PC, wC, hPA, hPC, ⟨hwC.1, fun E hE => ?_⟩, hwC⟩
    have hpE := prob_mem_Icc h𝒜.algebra hPA.1 hE
    rw [hwA.2 E hE, hφA _ hpE, hid _ hpE]
  · rintro ⟨PA, PC, w, hA, hC, hwA, hwC⟩
    exact reversed_implication 𝓔 pref U W h1 𝒜 𝒞 h𝒜 h𝒞 PA PC w hA hC hwA hwC
  · rintro ⟨PA, PC, w, hA, hC, hwA, hwC⟩
    exact ⟨insens_common h𝒜.algebra h𝒞.algebra hA.1 hC.1 hwA hwC ∅ univ,
      insens_common h𝒞.algebra h𝒜.algebra hC.1 hA.1 hwC hwA ∅ univ⟩

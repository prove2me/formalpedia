-- Prove2me | solution 1 for SourceTheory.Uniform.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:14:45.766529+00:00
-- url     : https://prove2.me/submissions/72141cee-418e-43fb-b328-63309a0e92a0

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace STUB1Aux

open Set SourceTheory.Uniform MeasureTheory

lemma bet_act {S Γ : Type*} {𝓔 : Set (Set S)} (h : IsSetAlgebra 𝓔) {E : Set S} (hE : E ∈ 𝓔)
    (γ β : Γ) : IsActFrom 𝓔 (bet γ E β) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Set.Finite.subset (Set.toFinite ({γ, β} : Set Γ))
    rintro _ ⟨s, rfl⟩
    unfold bet
    split_ifs <;> simp
  · intro α
    by_cases h1 : γ = α <;> by_cases h2 : β = α
    · have : bet γ E β ⁻¹' {α} = univ := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff, mem_univ, iff_true]
        split_ifs <;> simp_all
      rw [this]; exact h.univ_mem
    · have : bet γ E β ⁻¹' {α} = E := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff]
        split_ifs <;> simp_all
      rw [this]; exact hE
    · have : bet γ E β ⁻¹' {α} = Eᶜ := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff, mem_compl_iff]
        split_ifs <;> simp_all
      rw [this]; exact h.compl_mem hE
    · have : bet γ E β ⁻¹' {α} = ∅ := by
        ext s; simp only [bet, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        split_ifs <;> simp_all
      rw [this]; exact h.empty_mem

lemma W_le_of_null {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop}
    {U : Γ → ℝ} {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {X Y : Set S}
    (hX : X ∈ 𝓔) (hY : Y ∈ 𝓔) (hXY : X ⊆ Y) (hn : IsNull 𝓔 pref (Y \ X)) : W Y ≤ W X := by
  classical
  obtain ⟨α, β, -, hβα, -⟩ := h1.three_outcomes
  have hp := (hn (bet α X β) (bet α Y β) (bet_act h1.events hX α β) (bet_act h1.events hY α β)
    (by
      intro s hs
      simp only [mem_sdiff, not_and, not_not] at hs
      simp only [bet]
      by_cases h : s ∈ Y
      · simp [h, hs h]
      · have : s ∉ X := fun hx => h (hXY hx)
        simp [h, this])).1
  have := (h1.biseparable α β α β X hX Y hY hβα.le hβα.le).1 hp
  nlinarith

lemma W_strict {S Γ : Type*} {𝓔 : Set (Set S)} {pref : (S → Γ) → (S → Γ) → Prop}
    {U : Γ → ℝ} {W : Set S → ℝ} (h1 : Assumption1 𝓔 pref U W) {X Y H : Set S}
    (hX : X ∈ 𝓔) (hY : Y ∈ 𝓔) (hH : H ∈ 𝓔) (hXY : X ⊆ Y) (hYH : Y ∩ H = ∅)
    (hlt : W X < W Y) : W (X ∪ H) < W (Y ∪ H) := by
  classical
  obtain ⟨α, β, -, hβα, -⟩ := h1.three_outcomes
  have hA := h1.events
  have hZ : Y \ X ∈ 𝓔 := hA.sdiff_mem hY hX
  have hnn : ¬ IsNull 𝓔 pref (Y \ X) := fun hn => by
    have := W_le_of_null h1 hX hY hXY hn; linarith
  have hXH : X ∪ H ∈ 𝓔 := hA.union_mem hX hH
  have hYH' : Y ∪ H ∈ 𝓔 := hA.union_mem hY hH
  have hconst : ∀ s ∈ Y \ X, bet α (X ∪ H) β s = β := by
    intro s hs
    have hsH : s ∉ H := fun h => by
      have : s ∈ Y ∩ H := ⟨hs.1, h⟩
      rw [hYH] at this; exact this
    simp [bet, hs.2, hsH]
  have hrep : replaceOn (bet α (X ∪ H) β) (Y \ X) α = bet α (Y ∪ H) β := by
    funext s
    simp only [replaceOn, bet, mem_sdiff, mem_union]
    have hx : s ∈ X → s ∈ Y := fun h => hXY h
    by_cases g1 : s ∈ Y <;> by_cases g2 : s ∈ X <;> by_cases g3 : s ∈ H <;> simp_all
  have hsm := h1.strongMonotone (bet α (X ∪ H) β) (bet_act hA hXH α β) (Y \ X) hZ hnn β α
    hconst hβα
  rw [hrep] at hsm
  have hnp := hsm.2
  rw [h1.biseparable α β α β (X ∪ H) hXH (Y ∪ H) hYH' hβα.le hβα.le] at hnp
  push Not at hnp
  by_contra hc
  push Not at hc
  nlinarith

end STUB1Aux

open Set SourceTheory.Uniform MeasureTheory STUB1Aux

theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) (hpref : IsPreferredTo W 𝒮 𝒮)
    (B D : Set S) (hB : B ∈ 𝓔) (hD : D ∈ 𝓔) (hreg : IsRegularRegion W 𝒮 B D)
    (hins : IsMoreInsensitive W 𝒮 𝒮 B D) :
    ∀ E ∈ 𝒮, ∀ F ∈ 𝒮, ∀ H ∈ 𝒮, E ∩ H = ∅ → F ∩ H = ∅ →
      (W F ≤ W E ↔ W (F ∪ H) ≤ W (E ∪ H)) := by
  have hA := h𝒮.algebra
  have sub := h𝒮.subset
  have cr := h𝒮.convexRanged
  have Wnn : ∀ X ∈ 𝒮, 0 ≤ W X := fun X hX => by
    have := h1.W_mono X (sub hX) ∅ (sub hA.empty_mem) (empty_subset _)
    rw [h1.W_empty] at this; exact this
  have Wmono : ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, X ⊆ Y → W X ≤ W Y := fun X hX Y hY h =>
    h1.W_mono Y (sub hY) X (sub hX) h
  have peq : ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, W X = W Y → W Xᶜ = W Yᶜ := fun X hX Y hY h =>
    le_antisymm (hpref Y hY X hX h) (hpref X hX Y hY h.symm)
  have part3 : ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, X ∩ Y = ∅ → IsPartition3 𝒮 X (X ∪ Y)ᶜ Y := by
    intro X hX Y hY hXY
    have hXY' : ∀ s, s ∈ X → s ∈ Y → False := fun s h1 h2 => by
      have : s ∈ X ∩ Y := ⟨h1, h2⟩
      rw [hXY] at this; exact this
    refine ⟨hX, hA.compl_mem (hA.union_mem hX hY), hY, ?_, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]; intro s h1 h2; simp at h2; tauto
    · rw [Set.disjoint_left]; intro s h1 h2; exact hXY' s h1 h2
    · rw [Set.disjoint_left]; intro s h1 h2; simp at h1; tauto
    · ext s; simp; tauto
  -- equality transfer (proof of Lemma B.1, cases 1–3)
  have eqT : ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, ∀ Z ∈ 𝒮, X ∩ Z = ∅ → Y ∩ Z = ∅ → W X = W Y →
      (W B ≤ W Z ∨ W Zᶜ ≤ W D ∨ W B ≤ W X ∨ W Xᶜ ≤ W D) → W (X ∪ Z) = W (Y ∪ Z) := by
    intro X hX Y hY Z hZ hXZ hYZ hXY hc
    have hZX : Z ∩ X = ∅ := by rw [inter_comm]; exact hXZ
    have hZY : Z ∩ Y = ∅ := by rw [inter_comm]; exact hYZ
    have pX := part3 X hX Z hZ hXZ
    have pY := part3 Y hY Z hZ hYZ
    have qX := part3 Z hZ X hX hZX
    have qY := part3 Z hZ Y hY hZY
    have cXY := peq X hX Y hY hXY
    rcases hc with hc | hc | hc | hc
    · have a1 := (hins Z (Z ∪ X)ᶜ X Z (Z ∪ Y)ᶜ Y qX qY).2 hc rfl cXY.symm
      have a2 := (hins Z (Z ∪ Y)ᶜ Y Z (Z ∪ X)ᶜ X qY qX).2 hc rfl cXY
      simp only [compl_compl] at a1 a2
      rw [union_comm X Z, union_comm Y Z]; linarith
    · have a1 := (hins X (X ∪ Z)ᶜ Z Y (Y ∪ Z)ᶜ Z pX pY).1 hXY.symm rfl hc
      have a2 := (hins Y (Y ∪ Z)ᶜ Z X (X ∪ Z)ᶜ Z pY pX).1 hXY rfl hc
      have := peq _ (hA.compl_mem (hA.union_mem hX hZ)) _ (hA.compl_mem (hA.union_mem hY hZ))
        (le_antisymm a1 a2)
      simpa only [compl_compl] using this
    · have a1 := (hins Y (Y ∪ Z)ᶜ Z X (X ∪ Z)ᶜ Z pY pX).2 hc hXY rfl
      have a2 := (hins X (X ∪ Z)ᶜ Z Y (Y ∪ Z)ᶜ Z pX pY).2 (hXY ▸ hc) hXY.symm rfl
      simp only [compl_compl] at a1 a2
      linarith
    · have a1 := (hins Z (Z ∪ X)ᶜ X Z (Z ∪ Y)ᶜ Y qX qY).1 rfl cXY.symm hc
      have a2 := (hins Z (Z ∪ Y)ᶜ Y Z (Z ∪ X)ᶜ X qY qX).1 rfl cXY (cXY ▸ hc)
      have := peq _ (hA.compl_mem (hA.union_mem hZ hX)) _ (hA.compl_mem (hA.union_mem hZ hY))
        (le_antisymm a1 a2)
      simp only [compl_compl] at this
      rw [union_comm X Z, union_comm Y Z]; exact this
  -- strict transfer
  have st : ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, ∀ Z ∈ 𝒮, X ∩ Z = ∅ → Y ∩ Z = ∅ → W Y < W X →
      (W B ≤ W Z ∨ W Zᶜ ≤ W D ∨ W B ≤ W X ∨ W Xᶜ ≤ W D ∨ W B ≤ W Y ∨ W Yᶜ ≤ W D) →
      W (Y ∪ Z) < W (X ∪ Z) := by
    intro X hX Y hY Z hZ hXZ hYZ hlt hc
    have route1 : (W B ≤ W Z ∨ W Zᶜ ≤ W D ∨ W B ≤ W Y ∨ W Yᶜ ≤ W D) →
        W (Y ∪ Z) < W (X ∪ Z) := by
      intro hc'
      obtain ⟨X', hX', -, hX'X, hWX'⟩ := cr ∅ hA.empty_mem X hX (empty_subset _) (W Y)
        (by rw [h1.W_empty]; exact Wnn Y hY) hlt.le
      have hX'Z : X' ∩ Z = ∅ := by
        apply Set.eq_empty_of_subset_empty
        calc X' ∩ Z ⊆ X ∩ Z := inter_subset_inter_left _ hX'X
          _ = ∅ := hXZ
          _ ⊆ ∅ := le_rfl
      have e := eqT Y hY X' hX' Z hZ hYZ hX'Z hWX'.symm hc'
      have s := W_strict h1 (sub hX') (sub hX) (sub hZ) hX'X hXZ (by rw [hWX']; exact hlt)
      linarith
    have route2 : (W B ≤ W X ∨ W Xᶜ ≤ W D) → W (Y ∪ Z) < W (X ∪ Z) := by
      intro hc'
      have hYZc : Y ⊆ Zᶜ := by
        intro s hs hz
        have : s ∈ Y ∩ Z := ⟨hs, hz⟩
        rw [hYZ] at this; exact this
      have hXZc : X ⊆ Zᶜ := by
        intro s hs hz
        have : s ∈ X ∩ Z := ⟨hs, hz⟩
        rw [hXZ] at this; exact this
      obtain ⟨Y', hY', hYY', hY'Z, hWY'⟩ := cr Y hY Zᶜ (hA.compl_mem hZ) hYZc (W X) hlt.le
        (Wmono X hX Zᶜ (hA.compl_mem hZ) hXZc)
      have hY'Z' : Y' ∩ Z = ∅ := by
        ext s; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro h; exact hY'Z h
      have e := eqT X hX Y' hY' Z hZ hXZ hY'Z' hWY'.symm (by tauto)
      have s := W_strict h1 (sub hY) (sub hY') (sub hZ) hYY' hY'Z' (by rw [hWY']; exact hlt)
      linarith
    rcases hc with hc | hc | hc | hc | hc | hc
    · exact route1 (Or.inl hc)
    · exact route1 (Or.inr (Or.inl hc))
    · exact route2 (Or.inl hc)
    · exact route2 (Or.inr hc)
    · exact route1 (Or.inr (Or.inr (Or.inl hc)))
    · exact route1 (Or.inr (Or.inr (Or.inr hc)))
  have core : ∀ X ∈ 𝒮, ∀ Y ∈ 𝒮, ∀ Z ∈ 𝒮, X ∩ Z = ∅ → Y ∩ Z = ∅ →
      (W B ≤ W Z ∨ W Zᶜ ≤ W D ∨ W B ≤ W X ∨ W Xᶜ ≤ W D ∨ W B ≤ W Y ∨ W Yᶜ ≤ W D) →
      (W Y ≤ W X ↔ W (Y ∪ Z) ≤ W (X ∪ Z)) := by
    intro X hX Y hY Z hZ hXZ hYZ hc
    rcases lt_trichotomy (W Y) (W X) with h | h | h
    · have := st X hX Y hY Z hZ hXZ hYZ h hc
      exact ⟨fun _ => this.le, fun _ => h.le⟩
    · have e : W (Y ∪ Z) = W (X ∪ Z) := by
        rcases hc with hc | hc | hc | hc | hc | hc
        · exact eqT Y hY X hX Z hZ hYZ hXZ h (Or.inl hc)
        · exact eqT Y hY X hX Z hZ hYZ hXZ h (Or.inr (Or.inl hc))
        · exact (eqT X hX Y hY Z hZ hXZ hYZ h.symm (Or.inr (Or.inr (Or.inl hc)))).symm
        · exact (eqT X hX Y hY Z hZ hXZ hYZ h.symm (Or.inr (Or.inr (Or.inr hc)))).symm
        · exact eqT Y hY X hX Z hZ hYZ hXZ h (Or.inr (Or.inr (Or.inl hc)))
        · exact eqT Y hY X hX Z hZ hYZ hXZ h (Or.inr (Or.inr (Or.inr hc)))
      exact ⟨fun _ => e.le, fun _ => h.le⟩
    · have := st Y hY X hX Z hZ hYZ hXZ h (by tauto)
      exact ⟨fun h' => absurd h' (not_le.2 h), fun h' => absurd h' (not_le.2 this)⟩
  intro E hE F hF H hH hEH hFH
  by_cases hc : W B ≤ W H ∨ W Hᶜ ≤ W D ∨ W B ≤ W E ∨ W Eᶜ ≤ W D ∨ W B ≤ W F ∨ W Fᶜ ≤ W D
  · exact core E hE F hF H hH hEH hFH hc
  -- the remaining case: regularity
  have hEH' : ∀ s, s ∈ E → s ∈ H → False := fun s h1 h2 => by
    have : s ∈ E ∩ H := ⟨h1, h2⟩
    rw [hEH] at this; exact this
  have hFH' : ∀ s, s ∈ F → s ∈ H → False := fun s h1 h2 => by
    have : s ∈ F ∩ H := ⟨h1, h2⟩
    rw [hFH] at this; exact this
  set G := (E ∪ F ∪ H)ᶜ with hGdef
  have hG : G ∈ 𝒮 := hA.compl_mem (hA.union_mem (hA.union_mem hE hF) hH)
  have hFE : F \ E ∈ 𝒮 := hA.sdiff_mem hF hE
  obtain ⟨j, hj1, hj2⟩ := hreg ![E, F \ E, G, H]
    (by intro j; fin_cases j <;> simp [hE, hFE, hG, hH])
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> rw [Set.disjoint_left] <;> intro s <;>
        (try simp only [hGdef, mem_compl_iff, mem_union, mem_sdiff, not_or]) <;>
        (have := hEH' s; have := hFH' s; tauto))
    (by
      ext s; simp only [mem_iUnion, mem_univ, iff_true]
      by_cases h1 : s ∈ E
      · exact ⟨0, by simpa using h1⟩
      by_cases h2 : s ∈ F
      · exact ⟨1, by simp [h1, h2]⟩
      by_cases h3 : s ∈ H
      · exact ⟨3, by simpa using h3⟩
      · exact ⟨2, by simp [hGdef, h1, h2, h3]⟩)
  fin_cases j
  · simp at hj1; exact absurd (Or.inr (Or.inr (Or.inl hj1))) hc
  · simp at hj1
    have : W (F \ E) ≤ W F := Wmono _ hFE F hF diff_subset
    exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hj1.trans this)))))) hc
  · simp at hj1
    have hGH : G ∪ H ∈ 𝒮 := hA.union_mem hG hH
    have hBGH : W B ≤ W (G ∪ H) := hj1.trans (Wmono G hG _ hGH subset_union_left)
    have hEGH : E ∩ (G ∪ H) = ∅ := by
      ext s; simp only [hGdef, mem_inter_iff, mem_union, mem_compl_iff, mem_empty_iff_false, iff_false, not_or]; have := hEH' s; tauto
    have hFGH : F ∩ (G ∪ H) = ∅ := by
      ext s; simp only [hGdef, mem_inter_iff, mem_union, mem_compl_iff, mem_empty_iff_false, iff_false, not_or]; have := hFH' s; tauto
    have c1 := core E hE F hF (G ∪ H) hGH hEGH hFGH (Or.inl hBGH)
    have hEHG : (E ∪ H) ∩ G = ∅ := by ext s; simp [hGdef]; tauto
    have hFHG : (F ∪ H) ∩ G = ∅ := by ext s; simp [hGdef]; tauto
    have c2 := core (E ∪ H) (hA.union_mem hE hH) (F ∪ H) (hA.union_mem hF hH) G hG hEHG hFHG
      (Or.inl hj1)
    have r1 : F ∪ (G ∪ H) = (F ∪ H) ∪ G := by ext s; simp only [mem_union]; tauto
    have r2 : E ∪ (G ∪ H) = (E ∪ H) ∪ G := by ext s; simp only [mem_union]; tauto
    rw [c1, c2, r1, r2]
  · simp at hj1; exact absurd (Or.inl hj1) hc

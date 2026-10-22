-- Prove2me | solution 1 for SourceTheory.EqualSources.subadditive_pmatcher_inv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:09:42.326991+00:00
-- url     : https://prove2.me/submissions/496f2d71-7d79-4432-90ee-5ba8cf873635

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


theorem part3_of {S : Type*} {𝒮 : Set (Set S)} (h : MeasureTheory.IsSetAlgebra 𝒮) {S1 T : Set S}
    (h1 : S1 ∈ 𝒮) (hT : T ∈ 𝒮) (hsub : S1 ⊆ T) : IsPartition3 𝒮 S1 (T \ S1) Tᶜ := by
  refine ⟨h1, h.sdiff_mem hT h1, h.compl_mem hT, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]; intro x hx hx'; exact hx'.2 hx
  · rw [Set.disjoint_left]; intro x hx hx'; exact hx' (hsub hx)
  · rw [Set.disjoint_left]; intro x hx hx'; exact hx'  hx.1
  · ext x; simp only [mem_union, mem_diff, mem_compl_iff, mem_univ, iff_true]; tauto

theorem core {S : Type*} {𝓔 : Set (Set S)} {W : Set S → ℝ} {𝒳 𝒴 : Set (Set S)}
    (h𝒳 : IsSource 𝓔 W 𝒳) (h𝒴 : IsSource 𝓔 W 𝒴) {PX PY : Set S → ℝ} {wX wY : ℝ → ℝ}
    (hPX : IsProbOn 𝒳 PX) (hPY : IsProbOn 𝒴 PY)
    (hX : IsSourceFunction W 𝒳 PX wX) (hY : IsSourceFunction W 𝒴 PY wY) {B D : Set S}
    (hreg : IsRegularRegion W 𝒳 B D) (hins : IsMoreInsensitive W 𝒳 𝒴 B D)
    (ρ : ℝ → ℝ) (hρm : MapsTo ρ (Icc 0 1) (Icc 0 1)) (hρmono : MonotoneOn ρ (Icc 0 1))
    (hρw : ∀ p ∈ Icc (0:ℝ) 1, wX p = wY (ρ p)) (p ε : ℝ) (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (hpe : p + ε ≤ 1 / 2) : ρ (p + ε) - ρ p ≤ ρ ε := by
  obtain ⟨-, hD⟩ := reg4 h𝒳 hPX hX hreg
  have hAX := h𝒳.algebra
  have hAY := h𝒴.algebra
  have hP0 : PX ∅ = 0 := by
    have := prob_compl hAX hPX hAX.univ_mem
    rw [compl_univ, hPX.1] at this; linarith
  have hQ0 : PY ∅ = 0 := by
    have := prob_compl hAY hPY hAY.univ_mem
    rw [compl_univ, hPY.1] at this; linarith
  -- X side
  obtain ⟨A1, hA1, -, -, hPA1⟩ := ex_P h𝒳 hPX hX hAX.empty_mem hAX.univ_mem (empty_subset _)
    (q := p) (by rw [hP0]; exact hp) (by rw [hPX.1]; linarith)
  obtain ⟨T, hT, hA1T, -, hPT⟩ := ex_P h𝒳 hPX hX hA1 hAX.univ_mem (subset_univ _)
    (q := p + ε) (by rw [hPA1]; linarith) (by rw [hPX.1]; linarith)
  have hPA := part3_of hAX hA1 hT hA1T
  -- Y side
  have hp1 : p ∈ Icc (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hpe1 : p + ε ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hε1 : ε ∈ Icc (0:ℝ) 1 := ⟨hε, by linarith⟩
  have hρp := hρm hp1
  have hρpe := hρm hpe1
  have hρe := hρm hε1
  have hρle : ρ p ≤ ρ (p + ε) := hρmono hp1 hpe1 (by linarith)
  obtain ⟨C1, hC1, -, -, hPC1⟩ := ex_P h𝒴 hPY hY hAY.empty_mem hAY.univ_mem (empty_subset _)
    (q := ρ p) (by rw [hQ0]; exact hρp.1) (by rw [hPY.1]; exact hρp.2)
  obtain ⟨T', hT', hC1T, -, hPT'⟩ := ex_P h𝒴 hPY hY hC1 hAY.univ_mem (subset_univ _)
    (q := ρ (p + ε)) (by rw [hPC1]; exact hρle) (by rw [hPY.1]; exact hρpe.2)
  have hPC := part3_of hAY hC1 hT' hC1T
  have hWA1 : W A1 = W C1 := by
    rw [hX.2 _ hA1, hY.2 _ hC1, hPA1, hPC1]; exact hρw p hp1
  have hWT : W T = W T' := by
    rw [hX.2 _ hT, hY.2 _ hT', hPT, hPT']; exact hρw _ hpe1
  have hmonoX : MonotoneOn wX (Icc 0 1) := hX.1.1.2.1.monotoneOn
  have hWD : W T' ≤ W D := by
    rw [← hWT, hX.2 _ hT, hPT]
    refine le_trans ?_ hD
    exact hmonoX hpe1 ⟨by norm_num, by norm_num⟩ (by linarith)
  have := (hins C1 (T' \ C1) T'ᶜ A1 (T \ A1) Tᶜ hPC hPA).1 hWA1
    (by rw [compl_compl, compl_compl]; exact hWT) (by rw [compl_compl]; exact hWD)
  -- W (T' \ C1) ≤ W (T \ A1)
  have hm2 : T' \ C1 ∈ 𝒴 := hAY.sdiff_mem hT' hC1
  have hm2' : T \ A1 ∈ 𝒳 := hAX.sdiff_mem hT hA1
  rw [hY.2 _ hm2, hX.2 _ hm2', prob_diff hAY hPY hC1 hT' hC1T, prob_diff hAX hPX hA1 hT hA1T,
    hPT', hPC1, hPT, hPA1, show p + ε - p = ε by ring] at this
  rw [hρw ε hε1] at this
  have hmY := hY.1.1.2.1
  by_contra hcon
  push_neg at hcon
  have h1 : ρ ε < ρ (p + ε) - ρ p := hcon
  have := hmY ⟨hρe.1, hρe.2⟩ ⟨by linarith [hρp.2, hρpe.1, hρle], by linarith [hρp.1, hρpe.2]⟩ h1
  linarith

end MMC

theorem solution {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (B D : Set S) (hB : B ∈ 𝓔) (hD : D ∈ 𝓔)
    (hreg : SourceTheory.Uniform.IsRegularRegion W 𝒞 B D) (hins : SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 B D)
    (φ ψ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p))
    (hψ : ∀ p ∈ Icc (0 : ℝ) 1, ψ (φ p) = p ∧ φ (ψ p) = p) :
    ∀ p ε : ℝ, 0 ≤ p → 0 ≤ ε → p + ε ≤ 1 / 2 → ψ (p + ε) - ψ p ≤ ψ ε := by
  intro p ε hp hε hpe
  obtain ⟨⟨hmaps, hmono, h0, h1⟩, hcont⟩ := hφ
  have hψmem : ∀ q ∈ Icc (0:ℝ) 1, ψ q ∈ Icc (0:ℝ) 1 := by
    intro q hq
    have : q ∈ φ '' Icc (0:ℝ) 1 := by
      have := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hcont
      rw [h0, h1] at this
      exact this hq
    obtain ⟨r, hr, hrq⟩ := this
    have := (hψ r hr).1
    rw [hrq] at this
    rw [this]; exact hr
  have hψmono : MonotoneOn ψ (Icc 0 1) := by
    intro a ha b hb hab
    by_contra hlt
    push_neg at hlt
    have := hmono (hψmem b hb) (hψmem a ha) hlt
    rw [(hψ a ha).2, (hψ b hb).2] at this
    linarith
  have hw : ∀ q ∈ Icc (0:ℝ) 1, wC q = wA (ψ q) := by
    intro q hq
    rw [hφA _ (hψmem q hq), (hψ q hq).2]
  exact MMC.core h𝒞 h𝒜 h2.1.1 h2.2.1.1 h2.2.2.1 h2.2.2.2 hreg hins ψ hψmem hψmono hw p ε hp hε hpe

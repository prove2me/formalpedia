-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.unique_maximum_small_perturbation_on
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:42:34.801525+00:00
-- url     : https://prove2.me/submissions/64a95b8a-4326-49b7-8f96-a10e19be26f6

import Mathlib
set_option autoImplicit false
open Set

theorem solution {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : ContinuousOn f K) (hg : ContinuousOn g K) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (_hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∀ x ∈ K, f x + s * g x ≤ ε * s := by
  intro ε hε
  obtain ⟨xm,hxm,hmaxg⟩ := hK.exists_isMaxOn ⟨x₀,hx₀⟩ hg
  let T := K ∩ g ⁻¹' Ici ε
  have hTc : IsCompact T := hg.upperSemicontinuousOn.isCompact_inter_preimage_Ici hK ε
  by_cases hT : T.Nonempty
  · obtain ⟨y,hy,hymax⟩ := hTc.exists_isMaxOn hT (hf.mono (inter_subset_left))
    have hyne : y ≠ x₀ := by
      intro heq
      have hyε : ε ≤ g y := hy.2
      rw [heq,hgzero] at hyε
      linarith
    have hyneg : f y < 0 := by
      have hle := hfnonpos y hy.1
      have hne : f y ≠ 0 := by
        intro heq
        exact hyne (hunique y hy.1 heq)
      exact lt_of_le_of_ne hle hne
    let s₀ := (-f y) / (|g xm| + 1)
    have hden : 0 < |g xm| + 1 := by positivity
    have hs₀ : 0 < s₀ := div_pos (by linarith) hden
    refine ⟨s₀,hs₀,?_⟩
    intro s hs hs' x hx
    by_cases hgx : g x < ε
    · have hxnonpos := hfnonpos x hx
      nlinarith
    · have hxT : x ∈ T := ⟨hx,le_of_not_gt hgx⟩
      have hfx : f x ≤ f y := hymax hxT
      have hgm : g x ≤ g xm := hmaxg hx
      have hbound : g x ≤ |g xm| := hgm.trans (le_abs_self _)
      have hsden : s*(|g xm|+1) < -f y := (lt_div_iff₀ hden).mp hs'
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hbound)]
  · refine ⟨1,by norm_num,?_⟩
    intro s hs hs' x hx
    have hlt : g x < ε := by
      by_contra hnot
      exact hT ⟨x,hx,le_of_not_gt hnot⟩
    have hxnonpos := hfnonpos x hx
    nlinarith

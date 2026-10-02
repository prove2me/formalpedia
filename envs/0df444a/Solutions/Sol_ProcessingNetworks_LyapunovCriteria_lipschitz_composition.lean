-- Prove2me | solution 1 for ProcessingNetworks.LyapunovCriteria.lipschitz_composition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:17:26.138799+00:00
-- url     : https://prove2.me/submissions/5a68d3cf-2672-4327-9f98-c8e17a416f97

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn

open ProcessingNetworks.LyapunovCriteria

theorem solution {m : ℕ} (g : (Fin m → ℝ) → ℝ) (h : ℝ → Fin m → ℝ)
    (hg : IsLipschitzOn g Set.univ) (hh : IsLipschitzOn h (Set.Ici 0)) :
    IsLipschitzOn (fun t => g (h t)) (Set.Ici (0 : ℝ)) := by
  intro B hB
  obtain ⟨Kh, hKh⟩ := hh B hB
  have hsb : Bornology.IsBounded (Set.Ici (0 : ℝ) ∩ B) := hB.subset Set.inter_subset_right
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hsb
  have hbdd : Bornology.IsBounded (h '' (Set.Ici (0 : ℝ) ∩ B)) := by
    rw [Metric.isBounded_iff]
    refine ⟨(Kh : ℝ) * C, ?_⟩
    rintro x ⟨t, ht, rfl⟩ y ⟨t', ht', rfl⟩
    have h1 := hKh.dist_le_mul t ht t' ht'
    have h2 := hC ht ht'
    calc dist (h t) (h t') ≤ (Kh : ℝ) * dist t t' := h1
      _ ≤ (Kh : ℝ) * C := mul_le_mul_of_nonneg_left h2 Kh.coe_nonneg
  obtain ⟨Kg, hKg⟩ := hg (h '' (Set.Ici (0 : ℝ) ∩ B)) hbdd
  rw [Set.univ_inter] at hKg
  exact ⟨Kg * Kh, hKg.comp hKh (Set.mapsTo_image h _)⟩

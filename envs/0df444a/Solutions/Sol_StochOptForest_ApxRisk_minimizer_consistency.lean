-- Prove2me | solution 1 for StochOptForest.ApxRisk.minimizer_consistency
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:36:35.073907+00:00
-- url     : https://prove2.me/submissions/7a18464b-2962-4f6f-9ad5-da756e69ea60

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

open StochOptForest.ApxRisk in
theorem solution {d : ℕ} (g : Ed d → ℝ) (zbar : Ed d) (hg : Continuous g)
    (hmin : IsUniqueMin g zbar)
    (hlev : ∃ α : ℝ, g zbar < α ∧ Bornology.IsBounded {z | g z ≤ α}) :
    ∀ ε > 0, ∃ η > 0, ∀ h : Ed d → ℝ, (∀ z, |h z - g z| ≤ η) →
      ∀ z, (∀ w, h z ≤ h w) → ‖z - zbar‖ ≤ ε := by
  intro ε hε
  obtain ⟨α, hα, hb⟩ := hlev
  set A : Set (Ed d) := {z | ε ≤ ‖z - zbar‖} ∩ {z | g z ≤ α} with hAdef
  have hAc : IsCompact A := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply IsClosed.inter
      · exact isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
      · exact isClosed_le hg continuous_const
    · exact hb.subset Set.inter_subset_right
  have hβ : ∃ β, g zbar < β ∧ ∀ z, ε ≤ ‖z - zbar‖ → β ≤ g z := by
    rcases A.eq_empty_or_nonempty with hAe | hAne
    · refine ⟨α, hα, fun z hz => ?_⟩
      by_contra hlt
      push_neg at hlt
      have hzA : z ∈ A := ⟨hz, hlt.le⟩
      rw [hAe] at hzA
      exact hzA
    · obtain ⟨z0, hz0, hmin0⟩ := hAc.exists_isMinOn hAne hg.continuousOn
      refine ⟨min α (g z0), lt_min hα ?_, fun z hz => ?_⟩
      · rcases lt_or_eq_of_le (hmin.1 z0) with hlt | heq
        · exact hlt
        · exfalso
          have hglob : ∀ u, g z0 ≤ g u := fun u => heq ▸ hmin.1 u
          have hz0eq := hmin.2 z0 hglob
          have := hz0.1
          simp only [Set.mem_setOf_eq] at this
          rw [hz0eq, sub_self, norm_zero] at this
          linarith
      · by_cases hz' : g z ≤ α
        · exact (min_le_right _ _).trans (isMinOn_iff.mp hmin0 z ⟨hz, hz'⟩)
        · push_neg at hz'
          exact (min_le_left _ _).trans hz'.le
  obtain ⟨β, hβ1, hβ2⟩ := hβ
  refine ⟨(β - g zbar) / 3, by linarith, ?_⟩
  intro h hh z hz
  by_contra hne
  push_neg at hne
  have h0 := hβ2 z hne.le
  have h1 := abs_le.mp (hh z)
  have h2 := abs_le.mp (hh zbar)
  have h3 := hz zbar
  linarith [h1.1, h2.2]

-- Prove2me | solution 1 for PersistClust.Count.gap_excess
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T15:17:07.282466+00:00
-- url     : https://prove2.me/submissions/175a9f3a-30a9-409d-af5f-d90c3e60c999

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem solution {ε₀ : ℝ} (F : Finset ℝ) (hε : 0 < ε₀) (p : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ ε₀ ∧ ∀ τ ∈ F, τ ≠ p → δ₀ < |τ - p| := by
  classical
  set G : Finset ℝ := (F.filter (fun τ => τ ≠ p)).image (fun τ => |τ - p|) with hGdef
  by_cases hG : G.Nonempty
  · have hμmem : G.min' hG ∈ G := Finset.min'_mem _ hG
    obtain ⟨τ₀, hτ₀, hμeq⟩ := Finset.mem_image.mp hμmem
    have hτ₀ne : τ₀ ≠ p := (Finset.mem_filter.mp hτ₀).2
    have hμpos : 0 < G.min' hG := by
      rw [← hμeq]
      exact abs_pos.mpr (sub_ne_zero.mpr hτ₀ne)
    refine ⟨min ε₀ (G.min' hG) / 2, by positivity, by
      have h1 : min ε₀ (G.min' hG) ≤ ε₀ := min_le_left _ _
      linarith, fun τ hτ hτne => ?_⟩
    have hτmem : |τ - p| ∈ G :=
      Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hτne⟩, rfl⟩
    have hmin_le : G.min' hG ≤ |τ - p| := Finset.min'_le _ _ hτmem
    have h2 : min ε₀ (G.min' hG) ≤ G.min' hG := min_le_right _ _
    linarith [hμpos]
  · refine ⟨ε₀, hε, le_rfl, fun τ hτ hτne => ?_⟩
    exfalso
    exact hG ⟨|τ - p|, Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hτne⟩, rfl⟩⟩

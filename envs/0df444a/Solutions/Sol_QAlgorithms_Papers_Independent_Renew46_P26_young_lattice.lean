-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.young_lattice
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:49:52.365294+00:00
-- url     : https://prove2.me/submissions/f8cc530d-7246-4468-9743-4d37de74ae46

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

theorem solution (mu lam : YoungDiagram) : YoungEdge mu lam ↔ mu ⋖ lam := by
  constructor
  · rintro ⟨hle, hcard⟩
    have hsub : mu.cells ⊆ lam.cells := YoungDiagram.cells_subset_iff.mpr hle
    have hc := Finset.card_sdiff_of_subset hsub
    rw [hcard] at hc
    refine ⟨?_, ?_⟩
    · rw [← YoungDiagram.cells_ssubset_iff]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => ?_⟩
      rw [h] at hc; omega
    · intro c h1 h2
      rw [← YoungDiagram.cells_ssubset_iff] at h1 h2
      have := Finset.card_lt_card h1
      have := Finset.card_lt_card h2
      have := Finset.card_le_card hsub
      omega
  · rintro ⟨hlt, hcov⟩
    have hss : mu.cells ⊂ lam.cells := YoungDiagram.cells_ssubset_iff.mpr hlt
    refine ⟨hlt.le, ?_⟩
    have hne : (lam.cells \ mu.cells).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hss.2 h)
    by_contra hcard
    have h2 : 1 < (lam.cells \ mu.cells).card := by
      have := hne.card_pos; omega
    obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image (lam.cells \ mu.cells) (fun c => c.1 + c.2) hne
    obtain ⟨d, hd, hdc⟩ := Finset.exists_mem_ne h2 c
    rw [Finset.mem_sdiff] at hc hd
    let nu : YoungDiagram :=
      { cells := lam.cells.erase c
        isLowerSet := by
          intro b a hab hb
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hb ⊢
          refine ⟨lam.isLowerSet hab hb.1, ?_⟩
          rintro rfl
          have hbmu : b ∉ mu.cells := fun h => hc.2 (mu.isLowerSet hab h)
          have := hmax b (Finset.mem_sdiff.mpr ⟨hb.1, hbmu⟩)
          have h1 : a.1 ≤ b.1 := hab.1
          have h2 : a.2 ≤ b.2 := hab.2
          apply hb.2
          ext <;> omega }
    apply hcov (c := nu)
    · rw [← YoungDiagram.cells_ssubset_iff]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro x hx
        refine Finset.mem_erase.mpr ⟨?_, hss.1 hx⟩
        rintro rfl; exact hc.2 hx
      · intro h
        have : d ∈ nu.cells := Finset.mem_erase.mpr ⟨hdc, hd.1⟩
        rw [← h] at this
        exact hd.2 this
    · rw [← YoungDiagram.cells_ssubset_iff]
      exact Finset.erase_ssubset hc.1

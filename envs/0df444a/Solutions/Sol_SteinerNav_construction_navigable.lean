-- Prove2me | solution 1 for SteinerNav.construction_navigable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:04:17.045558+00:00
-- url     : https://prove2.me/submissions/11b61aba-8fc3-4a39-b62d-62f2c7a8346e

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_constructionEdges
import Theorems.Thm_SteinerNav_observation_4_3

open SteinerNav

theorem solution {d : ℕ} (α : ℝ) (hα : 1 < α) (P Q S : Finset (Pt d))
    (hQ : Q.Nonempty) (hQP : Q ⊆ P) (hS : ∀ q ∈ Q, CoversSet α q S P) :
    IsSteinerNavigable α P (S \ P) (constructionEdges P Q S) ∧
      (∀ x, (x, x) ∉ constructionEdges P Q S) ∧
      NoSteinerToSteiner (S \ P) P (constructionEdges P Q S) := by
  have hα_pos : 0 < α := by linarith
  have hnoloop : ∀ x, (x, x) ∉ constructionEdges P Q S := by
    intro x hx
    unfold constructionEdges at hx
    exact (Finset.mem_filter.mp hx).2 rfl
  have hnosteiner : NoSteinerToSteiner (S \ P) P (constructionEdges P Q S) := by
    intro x y hxy hxR
    have hxnotP : x ∉ P := (Finset.mem_sdiff.mp hxR).2
    unfold constructionEdges at hxy
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hxy).1 with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact (Finset.mem_product.mp h1).2
      · exact absurd (Finset.mem_product.mp h2).1 hxnotP
    · unfold type3Edges at h3
      exact absurd (Finset.mem_product.mp (Finset.mem_filter.mp h3).1).1 hxnotP
  refine ⟨⟨Finset.sdiff_disjoint, ?_, ?_⟩, hnoloop, hnosteiner⟩
  · intro x y hxy
    unfold constructionEdges at hxy
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hxy).1 with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨hxR, hyP⟩ := Finset.mem_product.mp h1
        exact ⟨Finset.mem_union_right P hxR, Finset.mem_union_left _ hyP⟩
      · obtain ⟨hxP, hyQS⟩ := Finset.mem_product.mp h2
        refine ⟨Finset.mem_union_left _ hxP, ?_⟩
        rcases Finset.mem_union.mp hyQS with hyQ | hyS
        · exact Finset.mem_union_left _ (hQP hyQ)
        · by_cases hyP : y ∈ P
          · exact Finset.mem_union_left _ hyP
          · exact Finset.mem_union_right P (Finset.mem_sdiff.mpr ⟨hyS, hyP⟩)
    · unfold type3Edges at h3
      obtain ⟨hxP, hyP⟩ := Finset.mem_product.mp (Finset.mem_filter.mp h3).1
      exact ⟨Finset.mem_union_left _ hxP, Finset.mem_union_left _ hyP⟩
  · intro s hs t ht hts
    have hcov_self : Covers α s t t := by
      unfold Covers
      rw [dist_self]
      exact div_pos (dist_pos.mpr hts.symm) hα_pos
    rcases Finset.mem_union.mp hs with hsP | hsR
    · by_cases htQ : t ∈ Q
      · refine ⟨t, ?_, hcov_self⟩
        unfold constructionEdges
        refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ?_), hts.symm⟩
        exact Finset.mem_product.mpr ⟨hsP, Finset.mem_union_left _ htQ⟩
      · obtain ⟨qt, hqtQ, hqt_min⟩ := Q.exists_min_image (fun q => dist q t) hQ
        by_cases hlt : dist s t < dist qt t
        · refine ⟨t, ?_, hcov_self⟩
          unfold constructionEdges
          refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _ ?_, hts.symm⟩
          unfold type3Edges
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsP, ht⟩, hts.symm, ?_⟩
          intro q hqQ
          exact lt_of_lt_of_le hlt (hqt_min q hqQ)
        · push_neg at hlt
          have ht_ne_qt : t ≠ qt := by
            intro heq
            subst heq
            exact htQ hqtQ
          obtain ⟨v, hvS, hcov_qt⟩ := hS qt hqtQ t ht ht_ne_qt
          have hcov_s : Covers α s v t :=
            SteinerNav.observation_4_3 α hα qt s v t hcov_qt hlt
          have hsv : s ≠ v := by
            intro heq
            subst heq
            unfold Covers at hcov_s
            have hpos : 0 < dist s t := dist_pos.mpr hts.symm
            have hlt1 : dist s t / α < dist s t := div_lt_self hpos hα
            linarith
          refine ⟨v, ?_, hcov_s⟩
          unfold constructionEdges
          refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ?_), hsv⟩
          exact Finset.mem_product.mpr ⟨hsP, Finset.mem_union_right _ hvS⟩
    · refine ⟨t, ?_, hcov_self⟩
      unfold constructionEdges
      refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ ?_), hts.symm⟩
      exact Finset.mem_product.mpr ⟨hsR, ht⟩

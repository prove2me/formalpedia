-- Prove2me | solution 1 for ProjSchedTW.Cumulative.exists_minimal_shortage_set
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:47:56.502773+00:00
-- url     : https://prove2.me/submissions/7ed7f148-8778-4923-aa9b-1559bb282f90

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

open ProjSchedTW.Cumulative in
theorem solution {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (hRem : BoundsStraddleZero P) (k : K) (F : Finset (Fin (n + 2)))
    (hF : IsShortageSet P k F) :
    ∃ F' : Finset (Fin (n + 2)), IsMinimalShortageSet P k F' ∧
      (F'.filter (fun j => P.r j k < 0)).Nonempty ∧
      F'.filter (fun j => P.r j k < 0) ⊆ F.filter (fun j => P.r j k < 0) ∧
      F.filter (fun j => 0 < P.r j k) ⊆ F'.filter (fun j => 0 < P.r j k) := by
  classical
  set C : Finset (Finset (Fin (n + 2))) := Finset.univ.filter (fun G =>
    IsShortageSet P k G ∧ G.filter (fun j => P.r j k < 0) ⊆ F.filter (fun j => P.r j k < 0) ∧
      F.filter (fun j => 0 < P.r j k) ⊆ G.filter (fun j => 0 < P.r j k)) with hC
  have hFC : F ∈ C := by
    rw [hC, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hF, Finset.Subset.refl _, Finset.Subset.refl _⟩
  obtain ⟨G, hGC, hGmin⟩ := Finset.exists_min_image C
    (fun G => (G.filter (fun j => P.r j k < 0)).card +
      ((Finset.univ \ G).filter (fun j => 0 < P.r j k)).card) ⟨F, hFC⟩
  rw [hC, Finset.mem_filter] at hGC
  obtain ⟨-, hGs, hGneg, hGpos⟩ := hGC
  refine ⟨G, ⟨hGs, ?_, ?_⟩, ?_, hGneg, hGpos⟩
  · rintro ⟨G', hsub, hG's, hdiff⟩
    have hmem : G' ∈ C := by
      rw [hC, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hG's, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_filter] at hx
        exact hGneg (Finset.mem_filter.2 ⟨hsub.1 hx.1, hx.2⟩)
      · intro x hx
        have h2 := hGpos hx
        rw [Finset.mem_filter] at h2 ⊢
        refine ⟨?_, h2.2⟩
        by_contra hx'
        have := hdiff x (Finset.mem_sdiff.2 ⟨h2.1, hx'⟩)
        omega
    have h1 := hGmin G' hmem
    obtain ⟨j, hjG, hjG'⟩ := Finset.exists_of_ssubset hsub
    have hjneg := hdiff j (Finset.mem_sdiff.2 ⟨hjG, hjG'⟩)
    have hlt : (G'.filter (fun j => P.r j k < 0)).card <
        (G.filter (fun j => P.r j k < 0)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨j, Finset.mem_filter.2 ⟨hjG, hjneg⟩, fun h => hjG' (Finset.mem_filter.1 h).1⟩
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hsub.1 hx.1, hx.2⟩
    have hle : ((Finset.univ \ G').filter (fun j => 0 < P.r j k)).card ≤
        ((Finset.univ \ G).filter (fun j => 0 < P.r j k)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨fun hxG => ?_, hx.2⟩
      have := hdiff x (Finset.mem_sdiff.2 ⟨hxG, hx.1⟩)
      omega
    omega
  · rintro ⟨G'', hsub, hG''s, hdiff⟩
    have hneg_sub : G''.filter (fun j => P.r j k < 0) ⊆ G.filter (fun j => P.r j k < 0) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨?_, hx.2⟩
      by_contra hxG
      have := hdiff x (Finset.mem_sdiff.2 ⟨hx.1, hxG⟩)
      omega
    have hmem : G'' ∈ C := by
      rw [hC, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hG''s, hneg_sub.trans hGneg, ?_⟩
      intro x hx
      have h2 := hGpos hx
      rw [Finset.mem_filter] at h2 ⊢
      exact ⟨hsub.1 h2.1, h2.2⟩
    have h1 := hGmin G'' hmem
    obtain ⟨j, hjG'', hjG⟩ := Finset.exists_of_ssubset hsub
    have hjpos := hdiff j (Finset.mem_sdiff.2 ⟨hjG'', hjG⟩)
    have hle := Finset.card_le_card hneg_sub
    have hlt : ((Finset.univ \ G'').filter (fun j => 0 < P.r j k)).card <
        ((Finset.univ \ G).filter (fun j => 0 < P.r j k)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨hjG, hjpos⟩
        · simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and]
          intro h; exact absurd hjG'' h
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨fun hxG => hx.1 (hsub.1 hxG), hx.2⟩
    omega
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hnn : 0 ≤ ∑ i ∈ G, P.r i k := by
      apply Finset.sum_nonneg
      intro i hi
      by_contra hneg0
      have hneg : P.r i k < 0 := lt_of_not_ge hneg0
      have hm : i ∈ G.filter (fun j => P.r j k < 0) := Finset.mem_filter.2 ⟨hi, hneg⟩
      rw [h] at hm
      simp at hm
    have h3 := hGs.2
    have h4 := (hRem k).1
    omega

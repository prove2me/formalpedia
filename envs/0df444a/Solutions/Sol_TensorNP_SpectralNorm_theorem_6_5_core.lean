-- Prove2me | solution 1 for TensorNP.SpectralNorm.theorem_6_5_core
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T04:59:52.516774+00:00
-- url     : https://prove2.me/submissions/92d7764b-ded9-42a8-8c57-cdf668ead40e

import Theorems.Thm_TensorNP_SpectralNorm_lemma_6_11
import Theorems.Thm_TensorNP_SpectralNorm_Tl_max_singular_value
import Mathlib.Tactic.Linarith

open TensorNP.SpectralNorm

theorem solution {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) :
    (∀ l : ℕ, 1 ≤ l →
        (specNorm (fun i j k => (cliqueTensor G ε l i j k : ℝ)) = 1 ↔ l = G.cliqueNum)) ∧
      IsUnitSingularValue (fun i j k => (cliqueTensor G ε G.cliqueNum i j k : ℝ)) 1 ∧
      (∀ l : ℕ, G.cliqueNum < l →
        ¬ IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) 1) ∧
      IsGreatest {l : ℕ | 1 ≤ l ∧ l ≤ v ∧
          IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) 1}
        G.cliqueNum  := by
  classical
  have hω : 1 ≤ G.cliqueNum := by
    have hc : G.IsClique (↑({⟨0, hv⟩} : Finset (Fin v)) : Set (Fin v)) := by simp
    simpa using hc.card_le_cliqueNum
  have hωv : G.cliqueNum ≤ v := by
    obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    simpa [hs.card_eq] using s.card_le_univ
  have hatω : IsUnitSingularValue (fun i j k => (cliqueTensor G ε G.cliqueNum i j k : ℝ)) 1 := by
    simpa only [(lemma_6_11 hv G ε G.cliqueNum hω).2.1.mpr rfl] using
      (Tl_max_singular_value hv G ε G.cliqueNum hω).2.1
  have hnosing : ∀ l : ℕ, G.cliqueNum < l →
      ¬ IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) 1 := by
    exact fun l hl hs =>
      (not_le_of_gt ((lemma_6_11 hv G ε l (hω.trans hl.le)).2.2.2.mpr hl))
        (by simpa using (Tl_max_singular_value hv G ε l (hω.trans hl.le)).2.2 1 hs)
  refine ⟨?_, hatω, hnosing, ?_⟩
  · intro l hl
    simpa only [(Tl_max_singular_value hv G ε l hl).1] using (lemma_6_11 hv G ε l hl).2.1
  · exact ⟨⟨hω, hωv, hatω⟩, fun l hl => le_of_not_gt (fun h => hnosing l h hl.2.2)⟩

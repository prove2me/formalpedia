-- Prove2me | solution 1 for StrongPerfectGraph.Main.basic_perfect
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:18:18.620636+00:00
-- url     : https://prove2.me/submissions/91ae51cb-ee5d-4412-83af-3b287bf8c262

import Mathlib
import Theorems.Thm_StrongPerfectGraph_Main_complement_perfect
import Theorems.Thm_StrongPerfectGraph_Main_line_graph_bipartite_perfect
import Theorems.Thm_StrongPerfectGraph_Main_double_split_perfect
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

open StrongPerfectGraph.Main

namespace SPGTBasic

/-- A 2-colourable graph has chromatic number equal to clique number. -/
lemma chromatic_eq_clique_of_colorable_two {W : Type*} [Finite W] (K : SimpleGraph W)
    (hK : K.Colorable 2) : K.chromaticNumber = (K.cliqueNum : ℕ∞) := by
  classical
  apply le_antisymm _ K.cliqueNum_le_chromaticNumber
  by_cases hbot : K = ⊥
  · subst hbot
    rcases isEmpty_or_nonempty W with hW | hW
    · simp [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]
    · rw [SimpleGraph.chromaticNumber_bot]
      obtain ⟨w⟩ := hW
      have : (⊥ : SimpleGraph W).IsClique (({w} : Finset W) : Set W) := by simp
      have h1 := this.card_le_cliqueNum
      simp at h1
      exact_mod_cast h1
  · obtain ⟨u, v, huv⟩ : ∃ u v, K.Adj u v := by
      by_contra h
      push Not at h
      exact hbot (by ext a b; simp [h a b])
    have hcl : K.IsClique (({u, v} : Finset W) : Set W) := by
      rw [Finset.coe_pair]; exact SimpleGraph.isClique_pair.mpr (fun _ => huv)
    have h2 := hcl.card_le_cliqueNum
    rw [Finset.card_pair huv.ne] at h2
    calc K.chromaticNumber ≤ 2 := hK.chromaticNumber_le
      _ ≤ (K.cliqueNum : ℕ∞) := by exact_mod_cast h2

/-- Bipartite graphs are perfect. -/
lemma bipartite_perfect {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsBipartite) :
    IsPerfect G := by
  intro X
  apply chromatic_eq_clique_of_colorable_two
  exact hG.of_hom (SimpleGraph.Embedding.induce X).toHom

end SPGTBasic

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBasic G) : IsPerfect G := by
  rcases hG with h | h | ⟨n, H, hH, ⟨e⟩⟩ | ⟨n, H, hH, ⟨e⟩⟩ | h
  · exact SPGTBasic.bipartite_perfect G h
  · simpa using complement_perfect Gᶜ (SPGTBasic.bipartite_perfect Gᶜ h)
  · exact line_graph_bipartite_perfect G H hH e
  · simpa using complement_perfect Gᶜ (line_graph_bipartite_perfect Gᶜ H hH e)
  · exact double_split_perfect G h

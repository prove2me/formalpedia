-- Prove2me | solution 1 for RepellingPairs.theorem_1_realizable_iff_repelling_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:56:56.810555+00:00
-- url     : https://prove2.me/submissions/b8620264-21e7-44a7-b5ac-082413450eaa

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_PathLength
import Definitions.Def_RepellingPairs_Repel
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_RealFlow
import Definitions.Def_RepellingPairs_IntegralFlow
import Theorems.Thm_RepellingPairs_lemma_5_intersecting_shortest_paths
import Theorems.Thm_RepellingPairs_farkas_alternative
import Theorems.Thm_RepellingPairs_flow_normalization
import Theorems.Thm_RepellingPairs_step_1_maximal_switching
import Theorems.Thm_RepellingPairs_cost_inequality
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Goal


open Multigraph in
theorem distG_eq {V : Type u} {E : Type v} (G : Multigraph V E) (ℓ : E → ℝ) {a b : V}
    (P : G.Path a b) (hP : P.1.IsShortest ℓ) : G.distG ℓ a b = ENNReal.ofReal (P.1.len ℓ) := by
  unfold Multigraph.distG
  apply le_antisymm
  · exact iInf_le _ P
  · exact le_iInf fun Q => ENNReal.ofReal_le_ofReal (hP Q)

end RepellingPairs.Dev.Goal

namespace RepellingPairs

theorem chk_theorem_1_realizable_iff_repelling_disjoint {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] (G : OSInstance V E k) (D : Fin k → Fin k → ℝ)
    (hD : IsMetric D) (hK : IsKalmanson D) (P : PathStructure G) :
    (∃ ℓ : E → ℝ, (∀ e, 0 ≤ ℓ e) ∧ ∀ i j,
        (P.path i j).1.len ℓ = D i j ∧
        ∀ Q : G.graph.Path (G.term i) (G.term j), (P.path i j).1.len ℓ ≤ Q.1.len ℓ) ↔
    ∀ i j i' j', Repel D i j i' j' →
      (P.path i j).1.VertexDisjoint (P.path i' j').1 := by
  classical
  constructor
  · rintro ⟨ℓ, hℓ0, hℓ⟩ i j i' j' hrep
    by_contra hnd
    have hnn : ∀ i j, 0 ≤ D i j := fun i j => by
      rw [← (hℓ i j).1]
      exact List.sum_nonneg (fun x hx => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact hℓ0 e)
    have hsh : ∀ i j, (P.path i j).1.IsShortest ℓ := fun i j => (hℓ i j).2
    have hd : ∀ i j, G.graph.distG ℓ (G.term i) (G.term j) = ENNReal.ofReal (D i j) := fun i j => by
      rw [Dev.Goal.distG_eq G.graph ℓ (P.path i j) (hsh i j), (hℓ i j).1]
    obtain ⟨h1, h2⟩ := lemma_5_intersecting_shortest_paths G.graph ℓ hℓ0 (P.path i j) (P.path i' j')
      (hsh i j) (hsh i' j') hnd
    rw [hd, hd, hd, hd] at h1 h2
    rw [← ENNReal.ofReal_add (hnn _ _) (hnn _ _), ← ENNReal.ofReal_add (hnn _ _) (hnn _ _),
      ENNReal.ofReal_le_ofReal_iff (add_nonneg (hnn _ _) (hnn _ _))] at h1 h2
    unfold Repel at hrep
    rw [hD.symm j i'] at h2
    rcases max_cases (D i i' + D j j') (D i j' + D i' j) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
      rw [hm] at hrep <;> linarith
  · intro hgood
    by_contra hno
    have hex := (not_not.1 (mt (farkas_alternative G D hD hK P).2 hno))
    obtain ⟨F, F', hF, hF', hload, hcost⟩ := hex
    obtain ⟨F₁, F₁', h2, h3, h4, hnt⟩ := flow_normalization G D hD hK P hgood F F' hF hF' hload hcost
    obtain ⟨F₂, h2', h3', h4', h5', _⟩ := step_1_maximal_switching G D hD hK P hgood F₁ F₁' h2 h3 h4
    have := cost_inequality G D hD hK P hgood F₂ F₁' h2' h4' h5'
    exact absurd h3' (not_lt.2 this)

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_theorem_1_realizable_iff_repelling_disjoint := @RepellingPairs.chk_theorem_1_realizable_iff_repelling_disjoint

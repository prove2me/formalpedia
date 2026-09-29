-- Prove2me | solution 1 for OnlinePrimalDual.GroupSteiner.lemma11_3
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:10:06.95302+00:00
-- url     : https://prove2.me/submissions/965cdb04-920a-4ee2-a887-23e15ceb278c

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_probHits

namespace OnlinePrimalDual.GroupSteiner

/-- The point mass at the empty cover. -/
def aux_l113_rho (E : Type*) [Fintype E] [DecidableEq E] : RandomCover E where
  p C := if C = ∅ then 1 else 0
  hp_nonneg C := by split_ifs <;> norm_num
  hp_sum := by
    rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset E) (fun _ => (1 : ℝ))]
    simp

theorem aux_l113_probHits_empty {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : RandomCover E) : ρ.probHits ∅ = 0 := by
  unfold RandomCover.probHits
  simp

end OnlinePrimalDual.GroupSteiner

open OnlinePrimalDual.GroupSteiner

theorem solution : ¬ (∃ α : ℝ, 0 < α ∧
      ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (vertexEdge : V → E) (ρ : RandomCover E) (N : ℕ) (hN : 2 ≤ N)
        (g : Finset V) (hg_le : g.card ≤ N) (wg : ℝ) (hwg : 1 ≤ wg),
        α / Real.log N ≤ ρ.probHits (g.image vertexEdge)) := by
  rintro ⟨α, hα, h⟩
  have key := @h PUnit PUnit _ _ _ _ (fun _ => PUnit.unit) (aux_l113_rho PUnit) 2 le_rfl ∅ (by simp) 1 le_rfl
  rw [Finset.image_empty, aux_l113_probHits_empty] at key
  have hlog : (0 : ℝ) < Real.log ((2 : ℕ) : ℝ) := by
    apply Real.log_pos; norm_num
  have : 0 < α / Real.log ((2 : ℕ) : ℝ) := div_pos hα hlog
  linarith

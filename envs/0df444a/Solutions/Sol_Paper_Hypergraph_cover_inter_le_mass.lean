-- Prove2me | solution 1 for Paper.Hypergraph.cover_inter_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:42.126254+00:00
-- url     : https://prove2.me/submissions/1f891087-f08e-4461-a702-05f19b32be4d

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {Z K : Finset ℕ} {γ : ℕ → ℝ}
    (hγ : H.Cover (indicator Z) γ) : H.setCoverCost (Z ∩ K) ≤
      ∑ e ∈ H.edges.filter (fun e => ¬ Disjoint (H.edge e) K), γ e := by
  let δ : ℕ → ℝ := fun e => if ¬ Disjoint (H.edge e) K then γ e else 0
  have hδ : H.Cover (indicator (Z ∩ K)) δ := by
    refine ⟨?_, ?_⟩
    · intro e he
      dsimp [δ]; split_ifs
      · exact le_rfl
      · exact hγ.1 e he
    · intro v hv
      by_cases hvZK : v ∈ Z ∩ K
      · have hh := hγ.2 v hv
        simp only [indicator, if_pos (mem_inter.mp hvZK).1] at hh
        simp only [indicator, if_pos hvZK]
        convert hh using 1
        apply sum_congr rfl
        intro e he
        exact if_pos (not_disjoint_iff.mpr ⟨v, (mem_filter.mp he).2, (mem_inter.mp hvZK).2⟩)
      · simp only [indicator, if_neg hvZK]
        apply sum_nonneg
        intro e he
        dsimp [δ]; split_ifs
        · exact le_rfl
        · exact hγ.1 e (mem_filter.mp he).1
  have hh := H.coverCost_le hδ
  simpa [setCoverCost, δ, sum_filter] using hh
end Paper.Hypergraph

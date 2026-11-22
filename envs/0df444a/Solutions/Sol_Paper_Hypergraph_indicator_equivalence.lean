-- Prove2me | solution 1 for Paper.Hypergraph.indicator_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:23.136341+00:00
-- url     : https://prove2.me/submissions/a7550459-6c55-4da7-8dbf-02531110a1d4

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_edgeDistance_indicator
import Theorems.Thm_Paper_Hypergraph_exists_component_of_mem
import Theorems.Thm_Paper_Hypergraph_indicator_balance_sum

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : H.EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1)
    {S : Finset ℕ} (hS : S ⊆ H.vertices) :
    H.FractionalBalanced γ θ (indicator S) ↔ H.IntegralBalanced γ θ S := by
  constructor
  · intro hfrac
    refine ⟨hS, ?_⟩
    intro K hK
    obtain ⟨u, huK, _⟩ := (mem_filter.mp hK).2
    have hKV := mem_powerset.mp (mem_filter.mp hK).1
    have huV := (mem_inter.mp (hKV huK)).1
    obtain ⟨e, he, hue⟩ := H.no_isolated u huV
    have hbal := hfrac.2 e he
    rw [H.indicator_balance_sum γ S he hue hK huK] at hbal
    linarith
  · intro hint
    refine ⟨?_, ?_⟩
    · intro v hv
      dsimp [indicator]
      split_ifs <;> norm_num
    · intro e he
      by_cases hES : H.edge e ⊆ S
      · have hsum : (∑ f ∈ H.edges, γ f * H.edgeDistance (indicator S) e f) =
            ∑ f ∈ H.edges, γ f := by
          apply sum_congr rfl
          intro f hf
          rw [H.edgeDistance_indicator S he hf]
          have hnot : ¬ ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
              u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v := by
            rintro ⟨u, hue, v, hvf, huS, _⟩
            exact huS (hES hue)
          rw [if_neg hnot, mul_one]
        rw [hsum]
        have hprod := mul_nonneg hθ.1.le hγ.2.le
        nlinarith
      · obtain ⟨u, hue, huS⟩ := Finset.not_subset.mp hES
        have huV := H.edge_subset e he hue
        have huJ : u ∈ (H.induce (H.vertices \ S)).vertices :=
          mem_inter.mpr ⟨huV, mem_sdiff.mpr ⟨huV, huS⟩⟩
        obtain ⟨K, hK, huK⟩ := (H.induce (H.vertices \ S)).exists_component_of_mem huJ
        rw [H.indicator_balance_sum γ S he hue hK huK]
        have hbal := hint.2 K hK
        linarith
end Paper.Hypergraph

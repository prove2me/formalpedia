-- Prove2me | solution 1 for Paper.Hypergraph.tree_weighted_median
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:10.049617+00:00
-- url     : https://prove2.me/submissions/daca04af-a9f5-42f0-a2e2-d2f226aedfb3

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
theorem _root_.solution {V I : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsTree) (E : Finset I) (a : I → V) (w : I → ℝ)
    (_hw : ∀ e ∈ E, 0 ≤ w e) :
    ∃ t, ∀ s, G.Adj t s →
      (∑ e ∈ E.filter (fun e => G.dist t (a e) = G.dist s (a e) + 1), w e) ≤
        (1 / 2 : ℝ) * ∑ e ∈ E, w e := by
  classical
  let F : V → ℝ := fun t => ∑ e ∈ E, w e * (G.dist t (a e) : ℝ)
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image univ F univ_nonempty
  refine ⟨t, ?_⟩
  intro s hts
  have hstep (e : I) :
      w e * (G.dist s (a e) : ℝ) = w e * (G.dist t (a e) : ℝ) + w e -
        2 * (if G.dist t (a e) = G.dist s (a e) + 1 then w e else 0) := by
    have hd := hG.dist_eq_dist_add_one_of_adj (a e) hts
    rw [SimpleGraph.dist_comm (u := a e) (v := t),
      SimpleGraph.dist_comm (u := a e) (v := s)] at hd
    split_ifs with h
    · have hc : (G.dist t (a e) : ℝ) = (G.dist s (a e) : ℝ) + 1 := by exact_mod_cast h
      rw [hc]
      ring
    · have hc : (G.dist s (a e) : ℝ) = (G.dist t (a e) : ℝ) + 1 := by
        exact_mod_cast hd.resolve_left h
      rw [hc]
      ring
  have heq : F s = F t + (∑ e ∈ E, w e) -
      2 * ∑ e ∈ E.filter (fun e => G.dist t (a e) = G.dist s (a e) + 1), w e := by
    dsimp [F]
    simp_rw [hstep]
    rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_filter]
  have hm := ht s (mem_univ s)
  linarith
end Paper.Hypergraph

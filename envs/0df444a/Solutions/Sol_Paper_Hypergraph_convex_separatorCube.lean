-- Prove2me | solution 1 for Paper.Hypergraph.convex_separatorCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:39.723533+00:00
-- url     : https://prove2.me/submissions/95149703-7a68-4590-a043-8fca5d60c82a

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_concave_finiteEdgeDistance

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (θ : ℝ) : Convex ℝ (H.separatorCube γ θ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_Icc (0 : ℕ → ℝ) 1 hx.1 hy.1 ha hb hab, ?_⟩
  intro e he
  have hc : a * (∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f x) +
      b * (∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f y) ≤
      ∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f (a • x + b • y) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro f hf
    have hd := (H.concave_finiteEdgeDistance e f).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have hh := mul_le_mul_of_nonneg_left hd (hγ f hf)
    dsimp [smul_eq_mul] at hh
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left (hx.2 e he) ha
  have h2 := mul_le_mul_of_nonneg_left (hy.2 e he) hb
  have hh := (add_le_add h1 h2).trans hc
  rwa [← add_mul, hab, one_mul] at hh
end Paper.Hypergraph

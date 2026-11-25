-- Prove2me | solution 1 for RegularSubgraph.val_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:22:10.804749+00:00
-- url     : https://prove2.me/submissions/bfd2cc81-f075-40c0-be4d-f9f996f19f03

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
variable {G p}
omit [Fintype V]
namespace RegularSubgraph
theorem _root_.solution (x : Edge G → ZMod p) (a b : V) : val G p x a b = val G p x b a := by
  unfold val
  by_cases h : G.Adj a b
  · simp only [h, h.symm, ↓reduceDIte]
    congr 2
    exact Sym2.eq_swap
  · have h' : ¬ G.Adj b a := fun h' => h h'.symm
    simp only [h, h', ↓reduceDIte]
end RegularSubgraph

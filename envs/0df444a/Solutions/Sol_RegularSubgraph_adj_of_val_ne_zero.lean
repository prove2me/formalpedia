-- Prove2me | solution 1 for RegularSubgraph.adj_of_val_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:22:13.281931+00:00
-- url     : https://prove2.me/submissions/251860f3-bd63-43cd-bfd1-80777cd6cf6b

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
theorem _root_.solution {x : Edge G → ZMod p} {a b : V} (h : val G p x a b ≠ 0) :
    G.Adj a b := by
  by_contra hab
  exact h (by simp [val, hab])
end RegularSubgraph

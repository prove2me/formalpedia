-- Prove2me | solution 1 for SimpleGraph.cliqueCountIn_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:43:04.196216+00:00
-- url     : https://prove2.me/submissions/42f9de4e-fea4-4573-856c-0c5d69c1367b

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ



set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {S S' : Finset V} (h : S ⊆ S') (k : ℕ) :
    G.cliqueCountIn S k ≤ G.cliqueCountIn S' k :=
  card_le_card fun T hT => by
    simp only [mem_filter, mem_powersetCard] at hT ⊢
    exact ⟨⟨hT.1.1.trans h, hT.1.2⟩, hT.2⟩
end SimpleGraph

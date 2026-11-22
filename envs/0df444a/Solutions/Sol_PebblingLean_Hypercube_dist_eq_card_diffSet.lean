-- Prove2me | solution 1 for PebblingLean.Hypercube.dist_eq_card_diffSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:06.703878+00:00
-- url     : https://prove2.me/submissions/18ce3734-4aa9-4ea3-a1bb-3af1a14896bd

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_Hypercube

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution {n : ℕ} (x y : HypercubeVertex n) :
    dist x y = (diffSet x y).card := by
  rfl
end PebblingLean.Hypercube

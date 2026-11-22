-- Prove2me | solution 1 for PebblingLean.Hypercube.dist_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:15:10.603889+00:00
-- url     : https://prove2.me/submissions/4c573c13-38a4-4f05-8e1e-b6fdd16ba7ec

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_Examples

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution (n : ℕ) : dist (zeroVertex n) (zeroVertex n) = 0 := by
  exact dist_self (zeroVertex n)
end PebblingLean.Hypercube

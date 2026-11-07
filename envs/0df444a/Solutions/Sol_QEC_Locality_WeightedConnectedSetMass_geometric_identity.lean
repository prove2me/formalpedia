-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.geometric_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:22:26.552002+00:00
-- url     : https://prove2.me/submissions/bc61213b-0976-4e37-8602-3399c9f99859

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (q : ℝ) (n : ℕ) :
    (1-q)*(∑ j ∈ Finset.range n, q^j) = 1-q^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith
end QEC.Locality.WeightedConnectedSetMass

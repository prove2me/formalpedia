-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.geometric_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:25.583454+00:00
-- url     : https://prove2.me/submissions/5ee7aa0b-bad6-4c17-a97f-8e57abc84fc1

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_geometric_identity

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (q : ℝ) (l n : ℕ) (hq : q<1) :
    geometric q l n = q^l*(1-q^n)/(1-q) := by
  have he := geometric_identity q n
  have hn : 1-q ≠ 0 := by linarith
  unfold geometric
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  apply (eq_div_iff hn).mpr
  calc
    (q^l*(∑ j ∈ Finset.range n, q^j))*(1-q) =
        q^l*((1-q)*(∑ j ∈ Finset.range n, q^j)) := by ring
    _ = q^l*(1-q^n) := by rw [he]
end QEC.Locality.WeightedConnectedSetMass

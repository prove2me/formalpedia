-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.prefix_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:43.426231+00:00
-- url     : https://prove2.me/submissions/b2841c5f-3eb1-4d6e-ae9e-45f6bd3c26bb

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
theorem _root_.solution (A b : ℝ) (l n : ℕ) (hA : A≠1) :
    b*(∑ j ∈ Finset.range n, A^(l+j)) = b*A^l*(A^n-1)/(A-1) := by
  have he := geometric_identity A n
  have he' : (A-1)*(∑ j ∈ Finset.range n, A^j)=A^n-1 := by linarith
  have hn : A-1≠0 := sub_ne_zero.mpr hA
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  apply (eq_div_iff hn).mpr
  calc
    (b*(A^l*(∑ j ∈ Finset.range n, A^j)))*(A-1) =
        b*A^l*((A-1)*(∑ j ∈ Finset.range n, A^j)) := by ring
    _ = b*A^l*(A^n-1) := by rw [he']
end QEC.Locality.WeightedConnectedSetMass

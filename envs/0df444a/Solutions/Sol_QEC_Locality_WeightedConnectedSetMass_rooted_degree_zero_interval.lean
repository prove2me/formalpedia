-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.rooted_degree_zero_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:55.124604+00:00
-- url     : https://prove2.me/submissions/d922c506-f854-4283-82cd-d2afc6586128

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_rooted_degree_zero_mass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_singleton_interval

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (G : SimpleGraph V)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}=0) (r : V) (a : V → ℝ) (L U : ℕ) :
    interval (fun m => rootedMass G r m a) L U = if L≤1 ∧ 1≤U then a r else 0 := by
  simp_rw [rooted_degree_zero_mass G hd]
  exact singleton_interval _ L U
end QEC.Locality.WeightedConnectedSetMass

-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.rooted_one_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:15.372921+00:00
-- url     : https://prove2.me/submissions/19a1c4a9-c08d-4bef-b499-7ed6fd81be46

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_rooted_one


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (G : SimpleGraph V) (r : V) (a : V → ℝ) :
    rootedMass G r 1 a = a r := by simp [rootedMass,rooted_one]
end QEC.Locality.WeightedConnectedSetMass

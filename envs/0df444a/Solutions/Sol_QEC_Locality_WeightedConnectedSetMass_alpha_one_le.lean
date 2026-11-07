-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.alpha_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:15:59.125194+00:00
-- url     : https://prove2.me/submissions/9c0595a8-0e1c-4c39-8d17-61ade64be895

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
theorem _root_.solution (Delta : ℕ) : 1 ≤ alpha Delta := by
  have h : (0 : ℝ) ≤ (Delta : ℝ) := Nat.cast_nonneg Delta
  unfold alpha
  nlinarith [sq_nonneg (Delta : ℝ)]
end QEC.Locality.WeightedConnectedSetMass

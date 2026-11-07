-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.singleton_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:22:24.361689+00:00
-- url     : https://prove2.me/submissions/de19f51d-bf0d-4835-a4f2-9b61db513313

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
theorem _root_.solution (x : ℝ) (L U : ℕ) :
    interval (fun m => if m=1 then x else 0) L U =
      if L≤1 ∧ 1≤U then x else 0 := by
  by_cases hL : L≤1
  · cases U with
    | zero => simp [interval]
    | succ U => simp [interval,hL]
  · have hl : 2 ≤ max 1 L := by omega
    have he : ∀ j : ℕ, max 1 L+j≠1 := by intro j; omega
    simp [interval,he,hL]
end QEC.Locality.WeightedConnectedSetMass

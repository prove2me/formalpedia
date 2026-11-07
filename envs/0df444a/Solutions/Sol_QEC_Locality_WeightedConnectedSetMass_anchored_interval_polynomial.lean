-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.anchored_interval_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:52:56.693852+00:00
-- url     : https://prove2.me/submissions/15a5df96-61d9-41b0-985e-edf7e9538c40

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_interval_mono
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_anchored_bounds

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R : Finset V)
    (a : V → ℝ) (b : ℝ) (hb : 0≤b) (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b)
    (L U : ℕ) :
    interval (fun m => anchoredMass G R m a) L U ≤
      (R.card : ℝ)*geometric (alpha Delta*b) (max 1 L) (U+1-max 1 L) := by
  calc
    _ ≤ interval (fun m => (R.card : ℝ)*(alpha Delta*b)^m) L U :=
      interval_mono _ _ L U (fun m _ => (anchored_bounds G Delta hd R m a b hb ha hab).2)
    _ = _ := by simp only [interval,geometric,Finset.mul_sum]
end QEC.Locality.WeightedConnectedSetMass

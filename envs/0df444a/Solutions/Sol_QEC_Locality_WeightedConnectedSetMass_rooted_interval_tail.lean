-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.rooted_interval_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:09.381068+00:00
-- url     : https://prove2.me/submissions/4f10fbe3-4749-49db-9b05-b01ccc58c8b7

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_alpha_one_le
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_interval_mono
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_rooted_bounds
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_geometric_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w}≤Delta) (r : V)
    (a : V → ℝ) (b : ℝ) (hb : 0≤b) (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b)
    (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => rootedMass G r m a) L U ≤
      (alpha Delta*b)^(max 1 L)/(1-alpha Delta*b) := by
  have h := interval_mono _ _ L U
    (fun m _ => (rooted_bounds G Delta hd r m a b hb ha hab).2)
  have hα : (0 : ℝ) ≤ alpha Delta := le_trans (by norm_num) (alpha_one_le Delta)
  have hq0 : (0 : ℝ) ≤ alpha Delta*b := mul_nonneg hα hb
  exact h.trans (geometric_le _ _ _ hq0 hq)
end QEC.Locality.WeightedConnectedSetMass

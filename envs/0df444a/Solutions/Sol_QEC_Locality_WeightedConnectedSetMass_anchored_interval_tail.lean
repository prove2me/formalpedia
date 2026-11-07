-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.anchored_interval_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:08.419082+00:00
-- url     : https://prove2.me/submissions/a43ae779-66a2-45fa-85f3-bdcdf3d97aaf

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_alpha_one_le
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_geometric_le
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_anchored_interval_polynomial

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
    (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => anchoredMass G R m a) L U ≤
      (R.card : ℝ)*(alpha Delta*b)^(max 1 L)/(1-alpha Delta*b) := by
  have h0 : 0≤alpha Delta*b := mul_nonneg (le_trans (by norm_num) (alpha_one_le Delta)) hb
  have hR : (0 : ℝ) ≤ (R.card : ℝ) := Nat.cast_nonneg R.card
  have hgeo :
      (R.card : ℝ)*geometric (alpha Delta*b) (max 1 L) (U+1-max 1 L) ≤
        (R.card : ℝ)*((alpha Delta*b)^(max 1 L)/(1-alpha Delta*b)) :=
    mul_le_mul_of_nonneg_left
      (geometric_le (alpha Delta*b) (max 1 L) (U+1-max 1 L) h0 hq) hR
  exact (anchored_interval_polynomial G Delta hd R a b hb ha hab L U).trans
    (by simpa only [mul_div_assoc] using hgeo)
end QEC.Locality.WeightedConnectedSetMass

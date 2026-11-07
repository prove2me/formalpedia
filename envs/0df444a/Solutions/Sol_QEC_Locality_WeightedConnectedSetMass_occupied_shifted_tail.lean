-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.occupied_shifted_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:53.290357+00:00
-- url     : https://prove2.me/submissions/99cdf487-0549-4292-9346-728ec4204699

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_alpha_one_le
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_geometric_le
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_interval_strong
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_structuralEnvelope_above

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (G : SimpleGraph V) (Delta : ℕ)
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta) (R B : Finset V)
    (hRB : Disjoint R B) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1)
    (L U : ℕ) (hL : B.card<L) (hp : 1≤L) :
    interval (fun m => occupiedMass G R B m a) L U ≤
      (R.card : ℝ)*alpha Delta^B.card*(alpha Delta*b)^(L-B.card)/(1-alpha Delta*b) := by
  have h := occupied_interval_strong G Delta hd R B hRB a b hb ha hab hq L U
  rw [structuralEnvelope_above _ _ _ L U hL hp] at h
  have h0 : 0≤alpha Delta*b := mul_nonneg (by linarith [alpha_one_le Delta]) hb
  have hn : 0 ≤ (R.card : ℝ)*alpha Delta^B.card :=
    mul_nonneg (Nat.cast_nonneg R.card)
      (pow_nonneg (le_trans (by norm_num) (alpha_one_le Delta)) _)
  exact h.trans (by simpa only [mul_assoc,mul_div_assoc] using
    mul_le_mul_of_nonneg_left (geometric_le _ _ _ h0 hq) hn)
end QEC.Locality.WeightedConnectedSetMass

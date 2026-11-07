-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.occupied_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:18.182083+00:00
-- url     : https://prove2.me/submissions/7ffd383d-7d56-43fd-9b8b-2401a1a59190

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_anchored_card_le
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_anchored

section
noncomputable section
namespace QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
private theorem product_bound (K : Finset V) (a : V → ℝ) (b : ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, a v ≤ b) :
    0 ≤ ∏ v ∈ K, a v ∧ (∏ v ∈ K, a v) ≤ b^K.card := by
  refine ⟨Finset.prod_nonneg (fun v _ => ha v), ?_⟩
  calc
    _ ≤ ∏ _v ∈ K, b := Finset.prod_le_prod (fun v _ => ha v) (fun v _ => hb v)
    _ = _ := by simp
end QEC.Locality.WeightedConnectedSetMass
end
end

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
    (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) :
    0≤occupiedMass G R B m a ∧
      occupiedMass G R B m a ≤ (R.card : ℝ)*(alpha Delta*(1+b))^m := by
  have hp : ∀ K ∈ anchored G R m, (∏ v ∈ K \ B, a v)≤(1+b)^m := by
    intro K hK
    have hm := ((mem_anchored G R m K).mp hK).1
    calc
      _ ≤ (1+b)^(K \ B).card :=
        (product_bound (K \ B) a (1+b) ha (fun v => by linarith [hab v])).2
      _ ≤ (1+b)^m := pow_le_pow_right₀ (by linarith)
        (hm ▸ Finset.card_le_card Finset.sdiff_subset)
  have hn : 0≤occupiedMass G R B m a :=
    Finset.sum_nonneg (fun K _ => Finset.prod_nonneg (fun v _ => ha v))
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∑ _K ∈ anchored G R m, (1+b)^m := Finset.sum_le_sum hp
    _ = ((anchored G R m).card : ℝ)*(1+b)^m := by simp
    _ ≤ ((R.card : ℝ)*alpha Delta^m)*(1+b)^m := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) m)
      unfold alpha
      exact_mod_cast (show (anchored G R m).card ≤ R.card*((Delta+1)^2)^m by
        rw [← pow_mul]
        exact anchored_card_le G Delta hd R m)
    _ = _ := by rw [mul_pow]; ring
end QEC.Locality.WeightedConnectedSetMass

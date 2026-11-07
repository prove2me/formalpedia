-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.anchored_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:51:31.578031+00:00
-- url     : https://prove2.me/submissions/a4f33ec9-a1f8-463c-9961-214e9b7bdaa5

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
omit [Fintype V] [DecidableEq V] in
private theorem weighted_count_bound (F : Finset (Finset V)) (m : ℕ)
    (hF : ∀ K ∈ F, K.card = m) (a : V → ℝ) (b : ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, a v ≤ b) :
    0 ≤ ∑ K ∈ F, ∏ v ∈ K, a v ∧
      (∑ K ∈ F, ∏ v ∈ K, a v) ≤ (F.card : ℝ)*b^m := by
  refine ⟨Finset.sum_nonneg (fun K _ => (product_bound K a b ha hb).1), ?_⟩
  calc
    _ ≤ ∑ _K ∈ F, b^m := by
      apply Finset.sum_le_sum
      intro K hK
      simpa only [hF K hK] using (product_bound K a b ha hb).2
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
    (hd : ∀ v, Nat.card {w : V // G.Adj v w} ≤ Delta)
    (R : Finset V) (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ v, 0 ≤ a v) (hab : ∀ v, a v ≤ b) :
    0 ≤ anchoredMass G R m a ∧
      anchoredMass G R m a ≤ (R.card : ℝ)*(alpha Delta*b)^m := by
  have hh := weighted_count_bound (anchored G R m) m
    (fun K hK => ((mem_anchored G R m K).mp hK).1) a b ha hab
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hc : ((anchored G R m).card : ℝ) ≤ (R.card : ℝ)*alpha Delta^m := by
    have hn := anchored_card_le G Delta hd R m
    unfold alpha
    exact_mod_cast (show (anchored G R m).card ≤ R.card*((Delta+1)^2)^m by
      rw [← pow_mul]
      exact hn)
  calc
    _ ≤ ((R.card : ℝ)*alpha Delta^m)*b^m :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hb _)
    _ = _ := by rw [mul_pow]; ring
end QEC.Locality.WeightedConnectedSetMass

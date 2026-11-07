-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.occupied_strong
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:51:33.980476+00:00
-- url     : https://prove2.me/submissions/4c26ab89-843e-47d7-8b9e-b0aca2aeb058

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_smallness
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
omit [Fintype V] in
private theorem remaining_card (K R B : Finset V) (m : ℕ) (hm : K.card=m)
    (hKR : (K∩R).Nonempty) (hRB : Disjoint R B) :
    max 1 (m-B.card) ≤ (K \ B).card := by
  have hpos : 1≤(K \ B).card := by
    apply Finset.one_le_card.mpr
    obtain ⟨v,hv⟩ := hKR
    have hvR := (Finset.mem_inter.mp hv).2
    have hvB : v∉B := fun hvB => (Finset.disjoint_left.mp hRB) hvR hvB
    exact ⟨v,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).1,hvB⟩⟩
  have he := Finset.card_sdiff_add_card_inter K B
  have hi : (K∩B).card≤B.card := Finset.card_le_card Finset.inter_subset_right
  omega
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
    (hRB : Disjoint R B) (m : ℕ) (a : V → ℝ) (b : ℝ) (hb : 0≤b)
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1) :
    occupiedMass G R B m a ≤ (R.card : ℝ)*alpha Delta^m*b^(max 1 (m-B.card)) := by
  have hb1 : b≤1 := (smallness Delta b hb hq).2.2.le
  calc
    _ ≤ ∑ _K ∈ anchored G R m, b^(max 1 (m-B.card)) := by
      apply Finset.sum_le_sum
      intro K hK
      obtain ⟨hm,hc,hKR⟩ := (mem_anchored G R m K).mp hK
      exact (product_bound (K \ B) a b ha hab).2.trans
        (pow_le_pow_of_le_one hb hb1 (remaining_card K R B m hm hKR hRB))
    _ = ((anchored G R m).card : ℝ)*b^(max 1 (m-B.card)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb _)
      unfold alpha
      exact_mod_cast (show (anchored G R m).card ≤ R.card*((Delta+1)^2)^m by
        rw [← pow_mul]
        exact anchored_card_le G Delta hd R m)
end QEC.Locality.WeightedConnectedSetMass

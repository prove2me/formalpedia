-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.occupied_interval_strong
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:53:12.782775+00:00
-- url     : https://prove2.me/submissions/ea3118b8-33b4-4cab-b544-42ccfdfaae5d

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_interval_mono
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_strong

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
    (ha : ∀ v, 0≤a v) (hab : ∀ v, a v≤b) (hq : alpha Delta*b<1) (L U : ℕ) :
    interval (fun m => occupiedMass G R B m a) L U ≤
      (R.card : ℝ)*structuralEnvelope (alpha Delta) b B.card L U := by
  have h := interval_mono _ _ L U
    (fun m _ => occupied_strong G Delta hd R B hRB m a b hb ha hab hq)
  apply h.trans_eq
  let l := max 1 L
  let F := Finset.range (U+1-l)
  let f := fun j => alpha Delta^(l+j)*b^(max 1 (l+j-B.card))
  have he : QEC.Locality.WeightedConnectedSetMass.interval
      (fun m => (R.card : ℝ)*alpha Delta^m*b^(max 1 (m-B.card))) L U =
      (R.card : ℝ)*∑ j ∈ F, f j := by
    simp only [interval,F,f,l,Finset.mul_sum,mul_assoc]
  rw [he]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not F (fun j => l+j≤B.card) f]
  unfold structuralEnvelope
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hc := (Finset.mem_filter.mp hj).2
    have hpow : max 1 (l+j-B.card)=1 := by omega
    simp only [f,hpow,pow_one]
    ring
  · have heq : F.filter (fun j => ¬l+j≤B.card) =
        F.filter (fun j => B.card<l+j) := by ext j; simp
    rw [heq]
    apply Finset.sum_congr rfl
    intro j hj
    have hc := (Finset.mem_filter.mp hj).2
    have hsum : B.card+(l+j-B.card)=l+j := by omega
    have hpow : max 1 (l+j-B.card)=l+j-B.card := by omega
    simp only [f,hpow,mul_pow]
    rw [← mul_assoc,← pow_add,hsum]
end QEC.Locality.WeightedConnectedSetMass

-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.traces_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:44.045847+00:00
-- url     : https://prove2.me/submissions/78d7136f-2233-40ec-a48d-ee47bc6fe01f

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
section
noncomputable section
namespace QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
private theorem next_card_le (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (r : V) :
    (next G r).card ≤ Delta+1 := by
  classical
  have hn : (Finset.univ.filter (G.Adj r)).card ≤ Delta := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hd r
  exact (Finset.card_insert_le r _).trans (Nat.add_le_add_right hn 1)
end QEC.Locality.ConnectedSetCounting
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (r : V) (n : Nat) :
    (traces G r n).card ≤ (Delta+1)^n := by
  classical
  induction n generalizing r with
  | zero => simp [traces]
  | succ n ih =>
    calc
      (traces G r (n+1)).card ≤ ∑ w ∈ next G r,
          ((traces G w n).image (List.cons r)).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ next G r, (Delta+1)^n := by
        apply Finset.sum_le_sum
        intro w hw
        exact Finset.card_image_le.trans (ih w)
      _ = (next G r).card * (Delta+1)^n := by simp
      _ ≤ (Delta+1)*(Delta+1)^n := Nat.mul_le_mul_right _ (next_card_le G Delta hd r)
      _ = (Delta+1)^(n+1) := by rw [pow_succ, Nat.mul_comm]
end QEC.Locality.ConnectedSetCounting

-- Prove2me | solution 1 for PetersenTheorem.three_mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:27:21.272538+00:00
-- url     : https://prove2.me/submissions/92d42efb-005a-4673-9232-cc8b2e926369

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Theorems.Thm_PetersenTheorem_three_le_outDarts

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace PetersenTheorem
theorem _root_.solution {ι : Type*} (h3 : G.IsRegularOfDegree 3)
    (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (O : Finset ι) (f : ι → Finset V) (T : Finset V)
    (hdisj : (O : Set ι).PairwiseDisjoint f) (hT : ∀ i ∈ O, Disjoint (f i) T)
    (hclosed : ∀ i ∈ O, ∀ x ∈ f i, ∀ y, G.Adj x y → y ∉ T → y ∈ f i)
    (hodd : ∀ i ∈ O, Odd (f i).card) :
    3 * O.card ≤ ∑ y ∈ T, (G.neighborFinset y \ T).card := by
  have step1 : 3 * O.card ≤ ∑ i ∈ O, ∑ x ∈ f i, (G.neighborFinset x ∩ T).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i hi => ?_
    refine (three_le_outDarts G h3 hb _ (hodd i hi)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x hx => ?_
    congr 1
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_inter, mem_neighborFinset]
    constructor
    · rintro ⟨hxy, hy⟩
      refine ⟨hxy, ?_⟩
      by_contra hyT
      exact hy (hclosed i hi x hx y hxy hyT)
    · rintro ⟨hxy, hy⟩
      exact ⟨hxy, fun hyi => Finset.disjoint_left.mp (hT i hi) hyi hy⟩
  rw [← Finset.sum_biUnion hdisj] at step1
  refine step1.trans ?_
  set U := O.biUnion f with hU
  have hUT : Disjoint U T := by
    rw [hU, Finset.disjoint_biUnion_left]; exact hT
  have e1 : ∀ x, (G.neighborFinset x ∩ T).card = ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
    intro x
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext y; simp [mem_neighborFinset, and_comm]
  simp only [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun y hy => ?_
  rw [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter] at hx
  simp only [Finset.mem_sdiff, mem_neighborFinset]
  exact ⟨hx.2.symm, fun hxT => Finset.disjoint_left.mp hUT hx.1 hxT⟩
end PetersenTheorem

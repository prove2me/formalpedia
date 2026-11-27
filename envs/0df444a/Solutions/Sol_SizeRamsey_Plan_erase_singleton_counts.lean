-- Prove2me | solution 1 for SizeRamsey.Plan.erase_singleton_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:28.420158+00:00
-- url     : https://prove2.me/submissions/d5f89fbe-6612-468f-86de-aaa586aa3ec3

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_tau4_erase_eq_of
public import Theorems.Thm_SizeRamsey_Plan_erase_edgeCount
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (v : V) :
    edgeCount (erase G {v}) + G.degree v = edgeCount G ∧
    edgeCount (erase G {v}) =
      edgeCount (G.deleteIncidenceSet v) ∧
    tau4 (erase G {v}) =
      tau4 (G.deleteIncidenceSet v) := by
  have h0 : edgeCount (G.induce ((({v} : Finset V)) : Set V)) = 0 := by
    rw [edgeCount_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have ha := a.2; have hb := b.2
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact he.ne (Subtype.ext (ha.trans hb.symm))
  have h1 : edgeCount (erase G {v}) + G.degree v = edgeCount G := by
    have := erase_edgeCount G {v}
    rw [Finset.sum_singleton, h0] at this
    exact this
  have hle : G.degree v ≤ edgeCount G := by omega
  refine ⟨h1, ?_, ?_⟩
  · have h2 : edgeCount (G.deleteIncidenceSet v) = edgeCount G - G.degree v := by
      rw [edgeCount_eq_card, edgeCount_eq_card, SimpleGraph.card_edgeFinset_deleteIncidenceSet]
    omega
  · refine tau4_erase_eq_of G _ {v} (fun f hf i => ?_) (fun a b ha hb => ?_)
    · obtain ⟨_, h01, h12, h23, h30⟩ := hf
      rw [Finset.mem_singleton]
      fin_cases i
      · exact (SimpleGraph.deleteIncidenceSet_adj.mp h01).2.1
      · exact (SimpleGraph.deleteIncidenceSet_adj.mp h12).2.1
      · exact (SimpleGraph.deleteIncidenceSet_adj.mp h23).2.1
      · exact (SimpleGraph.deleteIncidenceSet_adj.mp h30).2.1
    · rw [Finset.mem_singleton] at ha hb
      rw [SimpleGraph.deleteIncidenceSet_adj]
      exact ⟨fun h => h.1, fun h => ⟨h, ha, hb⟩⟩
end SizeRamsey.Plan

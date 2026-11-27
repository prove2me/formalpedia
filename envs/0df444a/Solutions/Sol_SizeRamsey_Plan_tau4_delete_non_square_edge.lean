-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_delete_non_square_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:24.484445+00:00
-- url     : https://prove2.me/submissions/80ec9fe5-cd99-400c-9f4f-bf818e0d0df6

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_isC4Map_iff_cyclic
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_edgeOnSquare
public import Theorems.Thm_SizeRamsey_Plan_tau4_eq_of_same_squares
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
theorem _root_.solution
    {u v : V} (hadj : G.Adj u v)
    (h : ¬ EdgeOnSquare G u v) :
    tau4 (G.deleteEdges {s(u, v)}) = tau4 G ∧
    edgeCount (G.deleteEdges {s(u, v)}) + 1 = edgeCount G := by
  refine ⟨tau4_eq_of_same_squares fun f => ⟨fun hf => ?_, fun hf => ?_⟩, ?_⟩
  · rw [isC4Map_iff_cyclic] at hf ⊢
    exact ⟨hf.1, fun i => (SimpleGraph.deleteEdges_adj.mp (hf.2 i)).1⟩
  · have hne : ∀ i, s(f i, f (i + 1)) ≠ s(u, v) := fun i heq => by
      obtain ⟨h1, h2⟩ := IsC4Map.edgeOnSquare hf i
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact h (ha ▸ hb ▸ h1)
      · exact h (ha ▸ hb ▸ h2)
    rw [isC4Map_iff_cyclic] at hf ⊢
    refine ⟨hf.1, fun i => SimpleGraph.deleteEdges_adj.mpr ⟨hf.2 i, ?_⟩⟩
    rw [Set.mem_singleton_iff]
    exact hne i
  · have hE : (G.deleteEdges {s(u, v)}).edgeFinset = G.edgeFinset.erase s(u, v) := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_diff,
        Set.mem_singleton_iff, Finset.mem_erase]
      tauto
    rw [edgeCount_eq_card, edgeCount_eq_card, hE, Finset.card_erase_of_mem
      (SimpleGraph.mem_edgeFinset.mpr hadj)]
    have : 0 < G.edgeFinset.card :=
      Finset.card_pos.mpr ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr hadj⟩
    omega
end SizeRamsey.Plan

-- Prove2me | solution 1 for SizeRamsey.Plan.mixed_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:43.170168+00:00
-- url     : https://prove2.me/submissions/5b776738-c4d7-415f-8abd-71d49757dda0

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_three_le_degree_of_adj
public import Theorems.Thm_SizeRamsey_Plan_two_mul_edgeCount_induce
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_adj_at
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_ne_at
public import Theorems.Thm_SizeRamsey_Plan_erase_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_tau4_delete_vertices_le


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
    {u v : V} (h : G.Adj u v)
    (hu : G.degree u = 2) (hv : G.degree v = 3) :
    tau4 G ≤ tau4 (erase G {u,v}) + 1 ∧
    edgeCount (erase G {u,v}) + 4 = edgeCount G := by
  have huv : u ≠ v := h.ne
  refine ⟨?_, ?_⟩
  · have hHit : HitsDeleted G {u, v} {v} := by
      intro g hg ⟨k, hk⟩
      by_cases hv' : ∃ i, g i = v
      · obtain ⟨i, hi⟩ := hv'
        exact ⟨i, by simp [hi]⟩
      · push Not at hv'
        exfalso
        have hk' : g k = u := by
          rcases Finset.mem_insert.mp hk with h' | h'
          · exact h'
          · exact absurd (Finset.mem_singleton.mp h') (hv' k)
        obtain ⟨h1, -, -, h3⟩ := IsC4Map.adj_at G hg k
        have hne := IsC4Map.ne_at G hg k (a := 1) (b := 3) (by decide)
        rw [hk'] at h1 h3
        have := three_le_degree_of_adj G h h1 h3.symm (hv' _).symm (hv' _).symm hne
        omega
    have := tau4_delete_vertices_le G {u, v} {v} (by simp) hHit
    simpa using this
  · have h1 := erase_edgeCount G {u, v}
    have h2 := two_mul_edgeCount_induce G {u, v}
    rw [Finset.sum_pair huv, hu, hv] at h1
    simp only [Finset.sum_pair huv, SimpleGraph.irrefl, h, h.symm, if_true, if_false] at h2
    omega
end SizeRamsey.Plan

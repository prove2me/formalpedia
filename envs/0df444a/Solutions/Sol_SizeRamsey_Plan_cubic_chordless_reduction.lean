-- Prove2me | solution 1 for SizeRamsey.Plan.cubic_chordless_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:38.183504+00:00
-- url     : https://prove2.me/submissions/99e15209-48b9-4241-a998-c13ae26091a1

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_four_le_degree_of_adj
public import Theorems.Thm_SizeRamsey_Plan_two_mul_edgeCount_induce
public import Theorems.Thm_SizeRamsey_Plan_sum_fin_four
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
    (f : Fin 4 → V)
    (hdeg : ∀ i, G.degree (f i) = 3)
    (hf : IsC4Map G f)
    (hac : ¬ G.Adj (f 0) (f 2))
    (hbd : ¬ G.Adj (f 1) (f 3)) :
    tau4 G ≤ tau4 (erase G (Finset.univ.image f)) + 2 ∧
    edgeCount (erase G (Finset.univ.image f)) + 8 =
      edgeCount G := by
  have hinj := hf.1
  obtain ⟨-, h01, h12, h23, h30⟩ := hf
  have hne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j h => hinj.ne h
  refine ⟨?_, ?_⟩
  · have hHit : HitsDeleted G (Finset.univ.image f) {f 0, f 2} := by
      intro g hg ⟨k, hk⟩
      by_contra hX
      push Not at hX
      have hX' : ∀ j, g j ≠ f 0 ∧ g j ≠ f 2 := fun j => by
        have := hX j; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
        exact this
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hk
      obtain ⟨g1, -, -, g3⟩ := IsC4Map.adj_at G hg k
      have hg13 := IsC4Map.ne_at G hg k (a := 1) (b := 3) (by decide)
      rw [← hm] at g1 g3
      have h02 := hne 0 2 (by decide)
      fin_cases m
      · exact (hX' k).1 hm.symm
      · have := four_le_degree_of_adj G h01.symm h12 g1 g3.symm h02 (hX' _).1.symm
          (hX' _).1.symm (hX' _).2.symm (hX' _).2.symm hg13
        have := hdeg 1; simp_all
      · exact (hX' k).2 hm.symm
      · have := four_le_degree_of_adj G h30 h23.symm g1 g3.symm h02 (hX' _).1.symm
          (hX' _).1.symm (hX' _).2.symm (hX' _).2.symm hg13
        have := hdeg 3; simp_all
    have hcard : ({f 0, f 2} : Finset V).card = 2 := Finset.card_pair (hne 0 2 (by decide))
    have := tau4_delete_vertices_le G (Finset.univ.image f) {f 0, f 2}
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) hHit
    omega
  · have h1 := erase_edgeCount G (Finset.univ.image f)
    have h2 := two_mul_edgeCount_induce G (Finset.univ.image f)
    rw [Finset.sum_image fun x _ y _ h => hinj h] at h1 h2
    simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    simp only [Finset.sum_image fun x _ y _ h => hinj h] at h2
    have hca : ¬ G.Adj (f 2) (f 0) := fun h => hac h.symm
    have hdb : ¬ G.Adj (f 3) (f 1) := fun h => hbd h.symm
    simp only [sum_fin_four, SimpleGraph.irrefl, h01, h12, h23, h30, h01.symm, h12.symm,
      h23.symm, h30.symm, hac, hbd, hca, hdb, ite_true, ite_false] at h2
    omega
end SizeRamsey.Plan

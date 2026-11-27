-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:17.918624+00:00
-- url     : https://prove2.me/submissions/36429915-ce6f-4d05-b3c6-a57f7aa8ab6b

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_mk
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_val
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4
public import Theorems.Thm_SizeRamsey_tau4_le_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution :
    tau4 G =
      ∑ C : G.ConnectedComponent, tau4 (compGraph G C) := by
  apply le_antisymm
  · choose T hT hcard using fun C : G.ConnectedComponent =>
      exists_transversal_card_eq_tau4 (compGraph G C)
    let S : Finset V := Finset.univ.biUnion fun C => (T C).map (Function.Embedding.subtype _)
    have hS : c4Transversal G S := by
      intro f hf
      set C := G.connectedComponentMk (f 0)
      have hmem : ∀ i, f i ∈ C.supp := by
        obtain ⟨_, h01, h12, h23, h30⟩ := hf
        have m0 : f 0 ∈ C.supp := rfl
        have m1 : f 1 ∈ C.supp := (C.mem_supp_congr_adj h01).mp m0
        have m2 : f 2 ∈ C.supp := (C.mem_supp_congr_adj h12).mp m1
        have m3 : f 3 ∈ C.supp := (C.mem_supp_congr_adj h23).mp m2
        intro i; fin_cases i
        exacts [m0, m1, m2, m3]
      obtain ⟨i, hi⟩ := hT C _ (IsC4Map.induce_mk hf hmem)
      refine ⟨i, Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ _, ?_⟩⟩
      exact Finset.mem_map.mpr ⟨_, hi, rfl⟩
    refine (tau4_le_card hS).trans (Finset.card_biUnion_le.trans ?_)
    exact (Finset.sum_congr rfl fun C _ => by rw [Finset.card_map, hcard C]).le
  · obtain ⟨T, hT, hcard⟩ := exists_transversal_card_eq_tau4 G
    have hC : ∀ C : G.ConnectedComponent, tau4 (compGraph G C) ≤
        (T.filter (fun v => G.connectedComponentMk v = C)).card := by
      intro C
      have hTC : c4Transversal (compGraph G C) (T.subtype (· ∈ C.supp)) := by
        intro f hf
        obtain ⟨i, hi⟩ := hT _ (IsC4Map.induce_val hf)
        exact ⟨i, Finset.mem_subtype.mpr hi⟩
      refine (tau4_le_card hTC).trans (le_of_eq ?_)
      rw [Finset.card_subtype]
      rfl
    rw [← hcard, Finset.card_eq_sum_card_fiberwise (f := G.connectedComponentMk)
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    exact Finset.sum_le_sum fun C _ => hC C
end SizeRamsey.Plan

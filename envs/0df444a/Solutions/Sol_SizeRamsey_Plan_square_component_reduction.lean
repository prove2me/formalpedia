-- Prove2me | solution 1 for SizeRamsey.Plan.square_component_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:08.216086+00:00
-- url     : https://prove2.me/submissions/f07b5672-453c-41cf-87fc-ebb9d2e2689a

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_adj_at
public import Theorems.Thm_SizeRamsey_IsC4Map_comp_iso
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_val
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_val
public import Theorems.Thm_SizeRamsey_Plan_compGraph_degree
public import Theorems.Thm_SizeRamsey_Plan_erase_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_induce_finset_degree_eq
public import Theorems.Thm_SizeRamsey_Plan_tau4_delete_vertices_le
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card
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
theorem _root_.solution
    (C : G.ConnectedComponent)
    (hiso : Nonempty
      (compGraph G C ≃g SimpleGraph.cycleGraph 4)) :
    tau4 G = tau4 (erase G C.supp.toFinset) + 1 ∧
    edgeCount (erase G C.supp.toFinset) + 4 =
      edgeCount G := by
  obtain ⟨φ⟩ := hiso
  set D := C.supp.toFinset with hDdef
  have hDmem : ∀ x, x ∈ D ↔ x ∈ C.supp := fun x => Set.mem_toFinset
  -- the square of the component
  let g : Fin 4 → V := fun i => (φ.symm i).val
  have hcyc : IsC4Map (SimpleGraph.cycleGraph 4) id :=
    ⟨Function.injective_id, by decide, by decide, by decide, by decide⟩
  have hg : IsC4Map G g := IsC4Map.induce_val (IsC4Map.comp_iso φ.symm hcyc)
  have hgD : ∀ i, g i ∈ D := fun i => (hDmem _).mpr (φ.symm i).2
  have hDg : D ⊆ Finset.univ.image g := by
    intro x hx
    refine Finset.mem_image.mpr ⟨φ ⟨x, (hDmem x).mp hx⟩, Finset.mem_univ _, ?_⟩
    simp [g]
  have hcardD : D.card ≤ 4 := (Finset.card_le_card hDg).trans Finset.card_image_le
  -- every square meeting D covers D
  have hcover : ∀ h : Fin 4 → V, IsC4Map G h → (∃ k, h k ∈ D) → Finset.univ.image h = D := by
    rintro h hh ⟨k, hk⟩
    have hk' := (hDmem _).mp hk
    obtain ⟨a1, a2, a3, -⟩ := IsC4Map.adj_at G hh k
    have m1 := (C.mem_supp_congr_adj a1).mp hk'
    have m2 := (C.mem_supp_congr_adj a2).mp m1
    have m3 := (C.mem_supp_congr_adj a3).mp m2
    have hall : ∀ i, h i ∈ D := by
      intro i
      have hi : i = k + (i - k) := (add_sub_cancel k i).symm
      rw [hi]
      generalize i - k = j
      fin_cases j
      · simpa using (hDmem _).mpr hk'
      · exact (hDmem _).mpr m1
      · exact (hDmem _).mpr m2
      · exact (hDmem _).mpr m3
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hall i
    · rw [Finset.card_image_of_injective _ hh.1]
      simpa using hcardD
  have hDeq : Finset.univ.image g = D := hcover g hg ⟨0, hgD 0⟩
  have hcard4 : D.card = 4 := by
    rw [← hDeq, Finset.card_image_of_injective _ hg.1]; simp
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · have hHit : HitsDeleted G D {g 0} := by
      intro h hh hmeet
      have := hcover h hh hmeet
      have h0 : g 0 ∈ Finset.univ.image h := this ▸ hgD 0
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h0
      exact ⟨i, Finset.mem_singleton.mpr hi⟩
    have := tau4_delete_vertices_le G D {g 0} (Finset.singleton_subset_iff.mpr (hgD 0)) hHit
    simpa using this
  · obtain ⟨T, hT, hTc⟩ := exists_transversal_card_eq_tau4 G
    obtain ⟨i, hi⟩ := hT g hg
    have hT' : c4Transversal (erase G D) (T.subtype (· ∉ D)) := by
      intro f hf
      obtain ⟨j, hj⟩ := hT _ (IsC4Map.erase_val hf)
      exact ⟨j, Finset.mem_subtype.mpr hj⟩
    have hlt : (T.filter (· ∉ D)).card < T.card :=
      Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨g i, hi, by simpa using hgD i⟩)
    have := tau4_le_card hT'
    rw [Finset.card_subtype] at this
    omega
  · have hdegC : ∀ x ∈ D, G.degree x = 2 := by
      intro x hx
      have hx' := (hDmem x).mp hx
      rw [← compGraph_degree G C ⟨x, hx'⟩]
      have h1 := φ.degree_eq ⟨x, hx'⟩
      have h2 : (SimpleGraph.cycleGraph 4).degree (φ ⟨x, hx'⟩) = 2 :=
        SimpleGraph.cycleGraph_degree_three_le (n := 1)
      convert h1.symm.trans h2 using 1
    have hnb : ∀ x ∈ D, (G.neighborFinset x).filter (· ∈ D) = G.neighborFinset x := by
      intro x hx
      refine Finset.filter_true_of_mem fun y hy => (hDmem y).mpr ?_
      exact (C.mem_supp_congr_adj ((G.mem_neighborFinset x y).mp hy)).mp ((hDmem x).mp hx)
    have hI : ∑ v ∈ D, ((G.neighborFinset v).filter (· ∈ D)).card =
        2 * edgeCount (G.induce (D : Set V)) := by
      rw [edgeCount_eq_card, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      rw [Finset.sum_subtype (p := (· ∈ D)) _ (by simp)]
      exact Finset.sum_congr rfl fun v _ => (induce_finset_degree_eq G D v).symm
    have hS : ∑ v ∈ D, G.degree v = 8 := by
      rw [Finset.sum_congr rfl hdegC, Finset.sum_const, hcard4]; rfl
    have hS' : ∑ v ∈ D, ((G.neighborFinset v).filter (· ∈ D)).card = 8 := by
      rw [← hS]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [hnb v hv, G.card_neighborFinset_eq_degree]
    have h1 := erase_edgeCount G D
    omega
end SizeRamsey.Plan

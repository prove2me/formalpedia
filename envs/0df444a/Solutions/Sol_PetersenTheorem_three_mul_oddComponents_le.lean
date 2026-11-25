-- Prove2me | solution 1 for PetersenTheorem.three_mul_oddComponents_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:33:29.2179+00:00
-- url     : https://prove2.me/submissions/1a55a3a0-64e9-474b-be4a-4427ca18b7d6

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
public import Theorems.Thm_PetersenTheorem_three_mul_card_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
namespace PetersenTheorem
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    {W : Type*} [Finite W] (H : SimpleGraph W) (S : Set W) (e : W ↪ V) (T : Finset V)
    (hdisjT : ∀ w, w ∉ S → e w ∉ T)
    (hclosed : ∀ w, w ∉ S → ∀ y, G.Adj (e w) y → y ∉ T → ∃ w', e w' = y ∧ H.Adj w w' ∧ w' ∉ S) :
    3 * ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤
      ∑ y ∈ T, (G.neighborFinset y \ T).card := by
  classical
  have := Fintype.ofFinite W
  set K := ((⊤ : H.Subgraph).deleteVerts S).coe with hK
  have hfin : K.oddComponents.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  let f : K.ConnectedComponent → Finset V := fun c =>
    (c.supp.toFinset.map (Function.Embedding.subtype _)).map e
  have hmem : ∀ c y, y ∈ f c ↔ ∃ w, ∃ hw : w ∈ ((⊤ : H.Subgraph).deleteVerts S).verts,
      K.connectedComponentMk ⟨w, hw⟩ = c ∧ e w = y := by
    intro c y
    simp [f, ConnectedComponent.mem_supp_iff]
  apply three_mul_card_le G h3 hb hfin.toFinset f T
  · intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨w, hw, rfl, rfl⟩ := (hmem _ _).mp hy
    obtain ⟨w', hw', rfl, he⟩ := (hmem _ _).mp hy'
    obtain rfl := e.injective he
    exact hcc' rfl
  · intro c _
    rw [Finset.disjoint_left]
    intro y hy
    obtain ⟨w, hw, rfl, rfl⟩ := (hmem _ _).mp hy
    exact hdisjT w (by simpa using hw)
  · intro c _ x hx y hadj hyT
    obtain ⟨w, hw, rfl, rfl⟩ := (hmem _ _).mp hx
    have hwS : w ∉ S := by simpa using hw
    obtain ⟨w', rfl, hadj', hw'S⟩ := hclosed w hwS y hadj hyT
    have hw' : w' ∈ ((⊤ : H.Subgraph).deleteVerts S).verts := by simpa using hw'S
    rw [hmem]
    refine ⟨w', hw', ?_, rfl⟩
    have hKadj : K.Adj ⟨w, hw⟩ ⟨w', hw'⟩ := by
      simp [hK, hwS, hw'S, hadj']
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hKadj).symm
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    simp only [f, Finset.card_map]
    rw [← Set.ncard_eq_toFinset_card']
    exact hc
end PetersenTheorem

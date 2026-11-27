-- Prove2me | solution 1 for SizeRamsey.Plan.component_attachment_card_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:26.178999+00:00
-- url     : https://prove2.me/submissions/b5391e13-5707-4436-8f78-a15a24ca8450

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components

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
    (hcon : G.Connected) (hsq : SquareSupported G)
    (D : Finset V) (hD : D.Nonempty)
    (hproper : D ≠ Finset.univ)
    (C : (erase G D).ConnectedComponent) :
    2 ≤ (attachmentEdges G D C).card := by
  have memCV : ∀ a, a ∈ componentVerts G D C ↔
      ∃ h : a ∉ D, (⟨a, h⟩ : {v : V // v ∉ D}) ∈ C.supp := by
    intro a; simp [componentVerts]
  have memAtt : ∀ a b, (a, b) ∈ attachmentEdges G D C ↔
      a ∈ componentVerts G D C ∧ b ∈ D ∧ G.Adj a b := by
    intro a b; simp [attachmentEdges, and_assoc]
  have stay : ∀ x y, x ∈ componentVerts G D C → G.Adj x y → y ∉ D →
      y ∈ componentVerts G D C := by
    intro x y hx hxy hy
    obtain ⟨hxD, hxC⟩ := (memCV x).mp hx
    refine (memCV y).mpr ⟨hy, ?_⟩
    exact (C.mem_supp_congr_adj (show (erase G D).Adj ⟨x, hxD⟩ ⟨y, hy⟩ from hxy)).mp hxC
  -- a first crossing edge
  obtain ⟨c0, hc0⟩ := C.nonempty_supp
  obtain ⟨d0, hd0⟩ := hD
  have hc0' : c0.val ∈ componentVerts G D C := (memCV _).mpr ⟨c0.2, hc0⟩
  have hd0' : d0 ∉ componentVerts G D C := fun h => ((memCV _).mp h).1 hd0
  obtain ⟨p⟩ := hcon.preconnected c0.val d0
  obtain ⟨⟨⟨x, y⟩, hxy⟩, -, hx, hy⟩ :=
    p.exists_boundary_dart (componentVerts G D C : Set V) hc0' hd0'
  simp only [Finset.mem_coe] at hx hy
  have hyD : y ∈ D := by
    by_contra hyD; exact hy (stay x y hx hxy hyD)
  have hxD : x ∉ D := ((memCV x).mp hx).1
  have e1 : (x, y) ∈ attachmentEdges G D C := (memAtt x y).mpr ⟨hx, hyD, hxy⟩
  -- the supporting square gives a second crossing
  obtain ⟨f, ⟨hinj, -, h12, h23, h30⟩, rfl, rfl⟩ := hsq hxy
  have hne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j hij => hinj.ne hij
  rw [Nat.succ_le_iff, Finset.one_lt_card]
  refine ⟨_, e1, ?_⟩
  by_cases h3 : f 3 ∈ D
  · refine ⟨(f 0, f 3), (memAtt _ _).mpr ⟨hx, h3, h30.symm⟩, ?_⟩
    intro h; exact hne 1 3 (by decide) (Prod.mk.inj h).2
  · have h3C := stay _ _ hx h30.symm h3
    by_cases h2 : f 2 ∈ D
    · refine ⟨(f 3, f 2), (memAtt _ _).mpr ⟨h3C, h2, h23.symm⟩, ?_⟩
      intro h; exact hne 0 3 (by decide) (Prod.mk.inj h).1
    · have h2C := stay _ _ h3C h23.symm h2
      refine ⟨(f 2, f 1), (memAtt _ _).mpr ⟨h2C, hyD, h12.symm⟩, ?_⟩
      intro h; exact hne 0 2 (by decide) (Prod.mk.inj h).1
end SizeRamsey.Plan

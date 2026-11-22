-- Prove2me | solution 1 for UlmsTheorem.kaplansky_extend_one_of_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:01:49.324748+00:00
-- url     : https://prove2.me/submissions/1aa24e71-ae17-4374-b70a-0a722ae8b193

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_adjoinElem_finite
public import Theorems.Thm_UlmsTheorem_socle_extend_build_map_heightPres
public import Theorems.Thm_UlmsTheorem_IsHeightPresOn_injective
public import Theorems.Thm_UlmsTheorem_IsHeightPreserving_injective
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    (hG : IsReducedPGroup p G)
    (s : UlmStage p (G := G) (H := H))
    {x : G} (hx_notin : x ∉ s.A) {w : H} {α : Ordinal.{0}}
    (hpxA : p • x ∈ s.A)
    (hpw : p • w = (s.e ⟨p • x, hpxA⟩ : H))
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p s.A x) (hwProper : IsProper p s.B w) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      x ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  obtain ⟨f, hfA, hfx, hfheight⟩ :=
    socle_extend_build_map_heightPres (p := p)
      s.e.toAddMonoidHom s.hφ hx_notin hpxA hpw
      hxα hxSucc hwα hwSucc hxProper hwProper
  let A' : AddSubgroup G := adjoinElem s.A x
  let raw : A' →+ H := (⊤ : AddSubgroup H).subtype.comp f
  let B' : AddSubgroup H := AddMonoidHom.range raw
  have hf_inj : Function.Injective f := IsHeightPresOn.injective (p := p) hG.reduced hfheight
  have hrange_inj : Function.Injective raw.rangeRestrict := fun a b hab ↦
    hf_inj (Subtype.ext (by simpa [raw] using congrArg Subtype.val hab))
  have hA'finite : Set.Finite (A' : Set G) := adjoinElem_finite (p := p) hG.primary s.hAfinite x
  let _ : Finite A' := hA'finite.to_subtype
  let s' : UlmStage p (G := G) (H := H) :=
    { A := A'
      B := B'
      hAfinite := hA'finite
      hBfinite := Set.finite_range raw
      e := AddEquiv.ofBijective raw.rangeRestrict
        ⟨hrange_inj, AddMonoidHom.rangeRestrict_surjective raw⟩
      hφ := fun a β ↦ by
        change ((a : A') : G) ∈ ulmSubgroup p β ↔
          (f a : H) ∈ ulmSubgroup p β
        exact hfheight a β }
  have hAA : s.A ≤ s'.A := le_adjoinElem s.A x
  -- Every old target element is the image of its own preimage, which the
  -- extension still sends where `s.e` did.
  have hBB : s.B ≤ s'.B := fun b hb ↦ by
    let a : s.A := s.e.symm ⟨b, hb⟩
    refine ⟨⟨(a : G), le_adjoinElem (A := s.A) (g := x) a.prop⟩, ?_⟩
    change (f ⟨(a : G), le_adjoinElem (A := s.A) (g := x) a.prop⟩ : H) = b
    rw [hfA a]
    simp [a]
  exact ⟨s', hAA, hBB, mem_adjoinElem_right s.A x, fun a ↦ hfA a⟩
end UlmsTheorem

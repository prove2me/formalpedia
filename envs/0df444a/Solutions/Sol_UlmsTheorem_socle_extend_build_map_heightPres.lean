-- Prove2me | solution 1 for UlmsTheorem.socle_extend_build_map_heightPres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:00:55.214569+00:00
-- url     : https://prove2.me/submissions/44e01d82-225e-45ee-a212-dcf80b814049

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
public import Theorems.Thm_UlmsTheorem_mem_adjoinElem_iff
public import Theorems.Thm_UlmsTheorem_socle_extend_build_map
public import Theorems.Thm_UlmsTheorem_proper_adjoin_rep_mem_iff
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
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {x : G} (hx_notin : x ∉ A) {w : H} {α : Ordinal.{0}}
    (hpxA : p • x ∈ A)
    (hpw : p • w = (φ ⟨p • x, hpxA⟩ : H))
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p A x) (hwProper : IsProper p B w) :
    ∃ φ' : adjoinElem A x →+ (⊤ : AddSubgroup H),
      (∀ a : A,
        (φ' ⟨a, le_adjoinElem (A := A) (g := x) a.prop⟩ : H) = φ a) ∧
      (φ' ⟨x, mem_adjoinElem_right (A := A) x⟩ : H) = w ∧
      IsHeightPresOn p φ' := by
  obtain ⟨φ', hφA, hφx⟩ :=
    socle_extend_build_map (p := p) φ hx_notin hpxA hpw
  refine ⟨φ', hφA, hφx, ?_⟩
  intro z β
  obtain ⟨a, haA, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := A) (g := x)).1 z.prop
  let aA : A := ⟨a, haA⟩
  let a' : adjoinElem A x :=
    ⟨a, le_adjoinElem (A := A) (g := x) haA⟩
  let x' : adjoinElem A x :=
    ⟨x, mem_adjoinElem_right (A := A) x⟩
  have hz : z = a' + n • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap :
      (φ' z : H) = (φ aA : H) + n • w := by
    rw [hz, map_add, map_zsmul]
    change (φ' a' : H) + n • (φ' x' : H) =
      (φ aA : H) + n • w
    rw [show (φ' a' : H) = φ aA by
      simpa [a', aA] using hφA aA]
    rw [show (φ' x' : H) = w by
      simpa [x'] using hφx]
  change (z : G) ∈ ulmSubgroup p β (G := G) ↔
    (φ' z : H) ∈ ulmSubgroup p β (G := H)
  rw [hmap, hz]
  change ((aA : G) + n • x ∈ ulmSubgroup p β (G := G)) ↔
    ((φ aA : H) + n • w ∈ ulmSubgroup p β (G := H))
  exact
    proper_adjoin_rep_mem_iff p φ hφ hxα hxSucc hwα hwSucc
      hxProper hwProper hpxA hpw aA n
end UlmsTheorem

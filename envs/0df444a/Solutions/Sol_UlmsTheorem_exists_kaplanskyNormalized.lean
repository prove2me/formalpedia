-- Prove2me | solution 1 for UlmsTheorem.exists_kaplanskyNormalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:30.662638+00:00
-- url     : https://prove2.me/submissions/bb0f99a8-675f-4b10-82b3-46cfa8479f9d

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
omit hp
namespace UlmsTheorem
theorem _root_.solution
    {A : AddSubgroup G} (hAfinite : Set.Finite (A : Set G)) (g : G) :
    ∃ x : G,
      x - g ∈ A ∧
      IsProper p A x ∧
      ∀ y : G, y - g ∈ A → IsProper p A y →
        ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by
  have hAne : (A : Set G).Nonempty := ⟨0, A.zero_mem⟩
  obtain ⟨a₀, ha₀A, ha₀max⟩ :=
    Set.exists_max_image (A : Set G) (fun a ↦ ulmHeight p (g + a))
      hAfinite hAne
  have ha₀proper : IsProper p A (g + a₀) := by
    intro a
    have haa : a₀ + (a : G) ∈ A := A.add_mem ha₀A a.prop
    simpa [add_assoc] using ha₀max (a₀ + (a : G)) haa
  let C : Set G := {a | a ∈ A ∧ IsProper p A (g + a)}
  have hCfinite : C.Finite :=
    hAfinite.subset (by
      intro a ha
      exact ha.1)
  have hCne : C.Nonempty := ⟨a₀, ha₀A, ha₀proper⟩
  obtain ⟨a, haC, hamax⟩ :=
    Set.exists_max_image C (fun a ↦ ulmHeight p (p • (g + a)))
      hCfinite hCne
  refine ⟨g + a, by simpa using haC.1, haC.2, ?_⟩
  intro y hyA hyProper
  have hyrepr : g + (y - g) = y := by abel
  have hyC : y - g ∈ C := by
    refine ⟨hyA, ?_⟩
    simpa [hyrepr] using hyProper
  simpa [hyrepr] using hamax (y - g) hyC
end UlmsTheorem

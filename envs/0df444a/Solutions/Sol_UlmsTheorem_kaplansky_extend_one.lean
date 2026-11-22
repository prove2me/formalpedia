-- Prove2me | solution 1 for UlmsTheorem.kaplansky_extend_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:03:17.638405+00:00
-- url     : https://prove2.me/submissions/138ee83f-ab74-43da-96ee-92fb3e01c1b5

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
public import Theorems.Thm_UlmsTheorem_exists_kaplanskyNormalized
public import Theorems.Thm_UlmsTheorem_kaplansky_extend_one_of_normalized
public import Theorems.Thm_UlmsTheorem_exists_ulmHeight_eq_of_ne_zero
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
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : UlmStage p (G := G) (H := H)) (g : G)
    (hpgA : p • g ∈ s.A) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  by_cases hgA : g ∈ s.A
  · exact ⟨s, le_rfl, le_rfl, hgA, fun _ ↦ rfl⟩
  obtain ⟨x, hxgA, hxProper, hpxMax'⟩ :=
    exists_kaplanskyNormalized (p := p) s.hAfinite g
  have hxA : x ∉ s.A := by
    intro hx
    apply hgA
    have : g = x - (x - g) := by abel
    rw [this]
    exact s.A.sub_mem hx hxgA
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxA
    simp [hx]
  have hpxA : p • x ∈ s.A := by
    have hdecomp : p • x = p • g + p • (x - g) := by
      rw [smul_sub]
      abel
    rw [hdecomp]
    exact s.A.add_mem hpgA (s.A.nsmul_mem hxgA p)
  obtain ⟨α, hxα, hxSucc⟩ :=
    exists_ulmHeight_eq_of_ne_zero (p := p) hG.reduced hx0
  have hpxMax :
      ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
        ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by
    intro y hyxA hyProper
    apply hpxMax' y
    · have : y - g = (y - x) + (x - g) := by abel
      rw [this]
      exact s.A.add_mem hyxA hxgA
    · exact hyProper
  obtain ⟨s', hAA, hBB, hxs', hext⟩ :=
    kaplansky_extend_one_of_normalized p hG s (hinv α) hxA hpxA
      hxα hxSucc hxProper hpxMax
  refine ⟨s', hAA, hBB, ?_, hext⟩
  have hxgA' : x - g ∈ s'.A := hAA hxgA
  have hgrepr : g = x - (x - g) := by abel
  rw [hgrepr]
  exact s'.A.sub_mem hxs' hxgA'
end UlmsTheorem

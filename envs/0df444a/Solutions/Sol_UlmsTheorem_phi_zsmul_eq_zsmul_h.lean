-- Prove2me | solution 1 for UlmsTheorem.phi_zsmul_eq_zsmul_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:27.720574+00:00
-- url     : https://prove2.me/submissions/d0211643-9c35-4fd3-baba-14018c00769a

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
public import Theorems.Thm_UlmsTheorem_dvd_of_zsmul_mem_of_not_mem
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
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    (k : ℤ) (hk : k • g ∈ A) :
    (↑(φ ⟨k • g, hk⟩) : H) = k • h := by
  obtain ⟨m, hm⟩ := dvd_of_zsmul_mem_of_not_mem (p := p) hg_notin hpg_in k hk
  calc
    (↑(φ ⟨k • g, hk⟩) : H)
        = (↑(φ ⟨m • (p • g), by
              simpa [hm, mul_zsmul, Int.mul_comm, Int.mul_left_comm,
                Int.mul_assoc] using hk⟩) : H) := by
            congr 2
            simp [hm, mul_zsmul, Int.mul_comm]
    _ = m • (↑(φ ⟨p • g, hpg_in⟩) : H) := by
          have hmap :
              φ ⟨m • (p • g), by
                exact A.zsmul_mem hpg_in m⟩ = m • φ ⟨p • g, hpg_in⟩ := by
            exact φ.map_zsmul m ⟨p • g, hpg_in⟩
          exact congrArg Subtype.val hmap
    _ = m • (p • h) := by
          rw [← hh_eq]
    _ = k • h := by
          simp [hm, mul_zsmul, Int.mul_comm]
end UlmsTheorem

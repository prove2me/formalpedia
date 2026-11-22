-- Prove2me | solution 1 for UlmsTheorem.proper_adjoin_rep_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:19.757573+00:00
-- url     : https://prove2.me/submissions/4a42351c-674d-4f3c-93fb-11a6fd2c7d10

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
public import Theorems.Thm_UlmsTheorem_not_mem_succ_add_zsmul_of_proper
public import Theorems.Thm_UlmsTheorem_add_zsmul_mem_iff_of_mem
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
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
    {x : G} {w : H} {α β : Ordinal.{0}}
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p A x) (hwProper : IsProper p B w)
    (hpxA : p • x ∈ A)
    (hpw : p • w = (φ ⟨p • x, hpxA⟩ : H))
    (a : A) (n : ℤ) :
    ((a : G) + n • x ∈ ulmSubgroup p β (G := G)) ↔
      ((φ a : H) + n • w ∈ ulmSubgroup p β (G := H)) := by
  by_cases hn : (p : ℤ) ∣ n
  · -- On multiples of `p` the representative rewrites inside `A`, where `φ`
    -- preserves height by hypothesis.
    obtain ⟨k, rfl⟩ := hn
    let a' : A := a + k • ⟨p • x, hpxA⟩
    have hxrepr : (a : G) + ((p : ℤ) * k) • x = (a' : G) := by
      change (a : G) + ((p : ℤ) * k) • x = (a : G) + k • (p • x)
      simp [mul_zsmul, Int.mul_comm]
    have hwrepr : (φ a : H) + ((p : ℤ) * k) • w = (φ a' : H) := by
      change (φ a : H) + ((p : ℤ) * k) • w = (φ (a + k • ⟨p • x, hpxA⟩) : H)
      rw [map_add, map_zsmul]
      push_cast
      rw [← hpw]
      simp [mul_zsmul, Int.mul_comm]
    rw [hxrepr, hwrepr]
    exact hφ a' β
  · by_cases hβα : β ≤ α
    · -- Below the exact height both `x` and `w` are already in the filtration,
      -- so the multiple is invisible on each side.
      rw [add_zsmul_mem_iff_of_mem p (ulmSubgroup_antitone p hβα hxα) n,
        add_zsmul_mem_iff_of_mem p (ulmSubgroup_antitone p hβα hwα) n]
      exact hφ a β
    · -- Above it, properness forbids either side from reaching `G_β`.
      have hsuccβ : Order.succ α ≤ β := Order.succ_le_iff.mpr (lt_of_not_ge hβα)
      exact iff_of_false
        (fun hmem ↦ not_mem_succ_add_zsmul_of_proper p hxα hxSucc hxProper hpxA a n hn
          (ulmSubgroup_antitone p hsuccβ hmem))
        (fun hmem ↦ not_mem_succ_add_zsmul_of_proper p hwα hwSucc hwProper
            (by rw [hpw]; exact (φ ⟨p • x, hpxA⟩).prop) (φ a) n hn
          (ulmSubgroup_antitone p hsuccβ hmem))
end UlmsTheorem

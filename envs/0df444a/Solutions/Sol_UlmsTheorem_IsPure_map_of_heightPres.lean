-- Prove2me | solution 1 for UlmsTheorem.IsPure.map_of_heightPres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:42.855921+00:00
-- url     : https://prove2.me/submissions/0967b95b-9f7f-4eb2-b0a4-161559e78d7f

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_nat
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


attribute [local simp] UlmsTheorem.pOrder_zero

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
namespace IsPure
theorem _root_.solution {A : AddSubgroup G} (hA : IsPure p A)
    (φ : G →+ H) (hφ : IsHeightPreserving p φ) :
    IsPure p (A.map φ) := by
  intro n x hx
  rcases x.property with ⟨a, haA, hax⟩
  have hx' : φ a ∈ pPow p n (G := H) := by
    simpa [hax] using hx
  rw [← ulmSubgroup_nat (p := p) n] at hx'
  have ha_pow : a ∈ pPow p n (G := G) := by
    rw [← ulmSubgroup_nat (p := p) n]
    exact (hφ a n).mpr hx'
  rcases hA n ⟨a, haA⟩ ha_pow with ⟨b, hb⟩
  refine ⟨⟨φ b, ⟨b, b.property, rfl⟩⟩, ?_⟩
  ext
  have hb' : p ^ n • (b : G) = a := congrArg (fun z : A ↦ (z : G)) hb
  exact (by
    simpa [map_nsmul] using (congrArg φ hb').trans hax)
end IsPure
end UlmsTheorem

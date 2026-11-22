-- Prove2me | solution 1 for UlmsTheorem.IsPure.range_of_heightPresOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:43.393891+00:00
-- url     : https://prove2.me/submissions/b269bbd6-6380-4c54-9f87-730b595d2326

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
theorem _root_.solution {A : AddSubgroup G} {B : AddSubgroup H}
    (hA : IsPure p A) (φ : A →+ B) (hφ : IsHeightPresOn p φ) :
    IsPure p ((⊤ : AddSubgroup A).map (B.subtype.comp φ)) := by
  intro n x hx
  rcases x.property with ⟨a, _haA, hax⟩
  have hx' : ((B.subtype.comp φ) a : H) ∈ pPow p n (G := H) := by
    simpa [hax] using hx
  rw [← ulmSubgroup_nat (p := p) (G := H) n] at hx'
  have ha_pow : (a : G) ∈ pPow p n (G := G) := by
    rw [← ulmSubgroup_nat (p := p) (G := G) n]
    exact (hφ a n).mpr hx'
  rcases hA n a ha_pow with ⟨b, hb⟩
  refine ⟨⟨(B.subtype.comp φ) b, ⟨b, by simp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  calc
    p ^ n • ((B.subtype.comp φ) b : H) = (B.subtype.comp φ) a := by
      simpa [AddMonoidHom.comp_apply, map_nsmul] using congrArg (B.subtype.comp φ) hb
    _ = (x : H) := by simpa using hax
end IsPure
end UlmsTheorem

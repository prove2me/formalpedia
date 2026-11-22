-- Prove2me | solution 1 for UlmsTheorem.ulmInvariant_iso_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:39.504842+00:00
-- url     : https://prove2.me/submissions/db2921ea-0d3a-4616-8f82-6d84e4146ec6

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Invariance
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Cardinal Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
namespace UlmsTheorem
theorem _root_.solution {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (α : Ordinal) :
    ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  let e := ulmQuotientMapIso p φ α
  have hlin : ∀ (c : ZMod p) (x : ulmQuotient p α (G := G)), e (c • x) = c • e x := by
    intro c x
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective c
    simp only [Nat.cast_smul_eq_nsmul]
    induction n with
    | zero => simp
    | succ n ih => simp only [succ_nsmul, map_add, ih]
  exact rank_eq_of_equiv_equiv (fun c : ZMod p ↦ c) e (by simp) hlin
end UlmsTheorem

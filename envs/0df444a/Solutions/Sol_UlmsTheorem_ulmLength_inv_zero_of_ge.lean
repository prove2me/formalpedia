-- Prove2me | solution 1 for UlmsTheorem.ulmLength.inv_zero_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:31.784326+00:00
-- url     : https://prove2.me/submissions/7184e05a-1f4e-4df8-96d8-01c619f6feed

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Theorems.Thm_UlmsTheorem_ulmLength_at_ulmLength
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
open UlmsTheorem.ulmLength
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem.ulmLength
theorem _root_.solution (hred : IsPReduced p G)
    (α : Ordinal) (hα : ulmLength p (G := G) ≤ α) :
    ulmInvariant p α (G := G) = 0 := by
  have hzero : ulmSubgroup p α (G := G) = ⊥ := by
    apply le_bot_iff.mp
    simpa [at_ulmLength (p := p) (hred := hred)] using
      (ulmSubgroup_antitone p hα : ulmSubgroup p α (G := G) ≤
        ulmSubgroup p (ulmLength p (G := G)) (G := G))
  have hpzero : pSocleAt p α (G := G) = ⊥ := by
    rw [pSocleAt, hzero]
    simp
  let _ : Subsingleton (pSocleAt p α (G := G)) := by
    rw [hpzero]
    infer_instance
  let _ : Subsingleton (ulmQuotient p α (G := G)) := by
    refine ⟨?_⟩
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    obtain rfl : a = b := Subsingleton.elim _ _
    rfl
  rw [ulmInvariant]
  exact rank_subsingleton' (R := ZMod p) (M := ulmQuotient p α (G := G))
end UlmsTheorem.ulmLength

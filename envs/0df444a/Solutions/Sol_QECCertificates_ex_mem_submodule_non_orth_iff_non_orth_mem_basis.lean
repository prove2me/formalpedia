-- Prove2me | solution 1 for QECCertificates.ex_mem_submodule_non_orth_iff_non_orth_mem_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:18.665127+00:00
-- url     : https://prove2.me/submissions/d1858249-4c80-4332-ad4b-0faf8a81afb1

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
namespace QECCertificates
theorem _root_.solution {n : ℕ}
    (S : Set (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
    (∃ y ∈ Submodule.span (ZMod 2) S, y ⬝ᵥ x = 1) ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_contra h
    have hzero : ∀ s ∈ S, s ⬝ᵥ x = 0 := by
      intro s hs
      rcases Fin.exists_fin_two.mp ⟨s ⬝ᵥ x, rfl⟩ with hz | ho
      · exact hz
      · exact False.elim (h ⟨s, hs, ho⟩)
    have hspan : ∀ z ∈ Submodule.span (ZMod 2) S, z ⬝ᵥ x = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact hzero z hz
      | zero => simp
      | add a b ha hb iha ihb => rw [add_dotProduct, iha, ihb, add_zero]
      | smul c a ha iha => rw [smul_dotProduct, iha, smul_zero]
    exact one_ne_zero (hyx.symm.trans (hspan y hy))
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, Submodule.subset_span hs, hsx⟩
end QECCertificates

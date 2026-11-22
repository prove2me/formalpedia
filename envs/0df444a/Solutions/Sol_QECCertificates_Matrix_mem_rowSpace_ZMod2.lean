-- Prove2me | solution 1 for QECCertificates.Matrix.mem_rowSpace_ZMod2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:30.646265+00:00
-- url     : https://prove2.me/submissions/9abdf7cf-69bd-43c2-9ad0-2c56910085f6

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
namespace Matrix
theorem _root_.solution {n₁ n₂ : ℕ}
  {M : Matrix (Fin n₁) (Fin n₂) (ZMod 2)}
  {x : Fin n₂ → (ZMod 2)} :
  x ∈ M.certificateRowSpace ↔
  ∃ (S : Finset ((Fin n₂) → (ZMod 2))),
    S ⊆ (Finset.image M Finset.univ) ∧ S.sum id = x := by
  constructor
  · intro hx
    have h_sum : ∀ (y : Fin n₂ → ZMod 2),
        y ∈ Submodule.span (ZMod 2) (Set.range M) →
        ∃ S : Finset (Fin n₂ → ZMod 2), S ⊆ Finset.image M Finset.univ ∧ S.sum id = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨ i, rfl ⟩ := hz
          refine ⟨ { M i }, ?_, ?_ ⟩
          · intro w hw
            rw [Finset.mem_singleton] at hw
            subst hw
            exact Finset.mem_image.mpr ⟨ i, Finset.mem_univ i, rfl ⟩
          · simp
      | zero => exact ⟨ ∅, by simp, by simp ⟩
      | add a b ha hb iha ihb =>
          obtain ⟨ S₁, hS₁, hS₁' ⟩ := iha
          obtain ⟨ S₂, hS₂, hS₂' ⟩ := ihb
          have hd : Disjoint (S₁ \ S₂) (S₂ \ S₁) := by
            apply Finset.disjoint_left.mpr
            intro z hz₁ hz₂
            rw [Finset.mem_sdiff] at hz₁ hz₂
            exact hz₂.2 hz₁.1
          have hsub : S₁ \ S₂ ∪ S₂ \ S₁ ⊆ Finset.image M Finset.univ := by
            intro z hz
            rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hz
            rcases hz with ⟨ h1, _ ⟩ | ⟨ h2, _ ⟩
            · exact hS₁ h1
            · exact hS₂ h2
          have h1 : (S₁ \ S₂).sum id + (S₁ ∩ S₂).sum id = a := by
            have hset : S₁ \ (S₁ ∩ S₂) = S₁ \ S₂ := by
              ext z; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
            rw [← hset, Finset.sum_sdiff (Finset.inter_subset_left : S₁ ∩ S₂ ⊆ S₁)]
            exact hS₁'
          have h2 : (S₂ \ S₁).sum id + (S₁ ∩ S₂).sum id = b := by
            have hset : S₂ \ (S₁ ∩ S₂) = S₂ \ S₁ := by
              ext z; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
            rw [← hset, Finset.sum_sdiff (Finset.inter_subset_right : S₁ ∩ S₂ ⊆ S₂)]
            exact hS₂'
          refine ⟨ S₁ \ S₂ ∪ S₂ \ S₁, hsub, ?_ ⟩
          rw [Finset.sum_union hd]
          have hzz : (S₁ ∩ S₂).sum id + (S₁ ∩ S₂).sum id = 0 := by
            funext i
            simp only [Pi.add_apply, Pi.zero_apply]
            rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]
          calc (S₁ \ S₂).sum id + (S₂ \ S₁).sum id
              = ((S₁ \ S₂).sum id + (S₂ \ S₁).sum id) +
                ((S₁ ∩ S₂).sum id + (S₁ ∩ S₂).sum id) := by rw [hzz, add_zero]
            _ = ((S₁ \ S₂).sum id + (S₁ ∩ S₂).sum id) +
                ((S₂ \ S₁).sum id + (S₁ ∩ S₂).sum id) := by abel
            _ = a + b := by rw [h1, h2]
      | smul c a ha iha =>
          obtain ⟨ S, hS, hS' ⟩ := iha
          rcases Fin.exists_fin_two.mp ⟨ c, rfl ⟩ with h | h
          · rw [h]
            refine ⟨ ∅, ?_, ?_ ⟩
            · intro z hz; simp at hz
            · ext i
              change (0 : ZMod 2) = (0 : ZMod 2) * a i
              ring
          · rw [h]
            refine ⟨ S, hS, ?_ ⟩
            rw [hS']
            ext i
            change a i = (1 : ZMod 2) * a i
            ring
    exact h_sum x hx
  · rintro ⟨ S, hS₁, hS₂ ⟩
    rw [← hS₂]
    exact Submodule.sum_mem _ fun s hs =>
      Submodule.subset_span <| Set.mem_range.mpr <| by
        obtain ⟨ i, -, hi ⟩ := Finset.mem_image.mp (hS₁ hs)
        exact ⟨ i, hi ⟩
end Matrix
end QECCertificates

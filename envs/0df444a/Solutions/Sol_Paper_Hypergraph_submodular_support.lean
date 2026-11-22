-- Prove2me | solution 1 for Paper.Hypergraph.submodular_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:48.882599+00:00
-- url     : https://prove2.me/submissions/ad55426a-1704-4df8-8578-e0d0e78c8225

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (U : Finset ℕ) (b : Finset ℕ → ℝ)
    (h0 : b ∅ = 0)
    (hm : ∀ A ⊆ U, ∀ B ⊆ U, A ⊆ B → b A ≤ b B)
    (hs : ∀ A ⊆ U, ∀ B ⊆ U, b (A ∪ B) + b (A ∩ B) ≤ b A + b B) :
    ∃ w : ℕ → ℝ, (∀ v, 0 ≤ w v) ∧ (∀ v ∉ U, w v = 0) ∧
      modularValue w U = b U ∧ ∀ A ⊆ U, modularValue w A ≤ b A := by
  induction U using Finset.induction_on generalizing b with
  | empty =>
    refine ⟨fun _ => 0, by simp, by simp, by simpa [modularValue] using h0.symm, ?_⟩
    intro A hA
    have : A = ∅ := subset_empty.mp hA
    simp [this, modularValue, h0]
  | @insert v U hv ih =>
    let g : Finset ℕ → ℝ := fun A => b (insert v A) - b {v}
    have hg0 : g ∅ = 0 := by simp [g]
    have hgm : ∀ A ⊆ U, ∀ B ⊆ U, A ⊆ B → g A ≤ g B := by
      intro A hA B hB hAB
      exact sub_le_sub_right (hm _ (insert_subset_insert v hA) _
        (insert_subset_insert v hB) (insert_subset_insert v hAB)) _
    have hgs : ∀ A ⊆ U, ∀ B ⊆ U,
        g (A ∪ B) + g (A ∩ B) ≤ g A + g B := by
      intro A hA B hB
      have h := hs (insert v A) (insert_subset_insert v hA)
        (insert v B) (insert_subset_insert v hB)
      have hi : insert v A ∩ insert v B = insert v (A ∩ B) := by
        ext u; simp only [mem_inter, mem_insert]; tauto
      simp only [insert_union, union_insert, insert_idem, hi] at h
      dsimp [g]
      linarith
    obtain ⟨w, hw, hwout, hwsum, hwle⟩ := ih g hg0 hgm hgs
    let z : ℕ → ℝ := fun u => if u = v then b {v} else w u
    have hbv : 0 ≤ b {v} := by
      have h := hm ∅ (empty_subset _) {v} (by simp) (empty_subset _)
      simpa [h0] using h
    have hzsum : ∀ A ⊆ U, modularValue z A = modularValue w A := by
      intro A hA
      apply sum_congr rfl
      intro u hu
      have huv : u ≠ v := by intro heq; subst u; exact hv (hA hu)
      simp only [z, if_neg huv]
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · intro u; dsimp [z]; split_ifs <;> first | exact hbv | exact hw u
    · intro u hu
      have huv : u ≠ v := by intro h; subst u; exact hu (mem_insert_self _ _)
      have huU : u ∉ U := fun h => hu (mem_insert_of_mem h)
      simp [z, huv, hwout u huU]
    · change (∑ u ∈ insert v U, z u) = _
      rw [sum_insert hv]
      change z v + modularValue z U = _
      rw [hzsum U (Subset.refl U), hwsum]
      simp [z, g]
    · intro A hA
      by_cases hvA : v ∈ A
      · have hAU : A.erase v ⊆ U := by
          intro u hu
          have huA := (mem_erase.mp hu).2
          rcases mem_insert.mp (hA huA) with h | h
          · exact False.elim ((mem_erase.mp hu).1 h)
          · exact h
        have hle := hwle (A.erase v) hAU
        dsimp [g] at hle
        rw [insert_erase hvA] at hle
        calc
          modularValue z A = z v + modularValue z (A.erase v) := by
            simpa [modularValue, add_comm] using (sum_erase_add A z hvA).symm
          _ = b {v} + modularValue w (A.erase v) := by
            rw [hzsum _ hAU]; simp [z]
          _ ≤ b A := by linarith
      · have hAU : A ⊆ U := by
          intro u hu
          rcases mem_insert.mp (hA hu) with h | h
          · subst u; exact False.elim (hvA hu)
          · exact h
        rw [hzsum A hAU]
        have hle := hwle A hAU
        have hsub := hs {v} (by simp) A hA
        have hinter : ({v} : Finset ℕ) ∩ A = ∅ := by simp [hvA]
        simp only [singleton_union, hinter, h0, add_zero] at hsub
        dsimp [g] at hle
        linarith
end Paper.Hypergraph

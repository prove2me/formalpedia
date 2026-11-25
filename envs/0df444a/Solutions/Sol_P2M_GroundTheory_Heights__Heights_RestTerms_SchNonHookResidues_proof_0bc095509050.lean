-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchNonHookResidues_proof_0bc095509050
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:41.311142+00:00
-- url     : https://prove2.me/submissions/033927db-34e2-493c-9e8f-fa73f0a174a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchNonHookResidues
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_sum_fin_staircase_57c59d30c9c9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchNonHookResidues
theorem _root_.solution (h1 : SchResidueCount.Statement) :
    SchNonHookResidues.Statement := by
  intro k nu hk hanti hsum hnot
  push Not at hnot
  obtain ⟨j, hj0, hj2⟩ := hnot
  have hk2 : 2 ≤ k := by have := j.isLt; omega
  by_contra hcon
  push Not at hcon
  set l : Fin k → ℕ := fun i => nu i + (k - 1 - (i : ℕ)) with hl
  have hinj : Function.Injective (fun i => l i % k) := by
    intro a b hab
    by_contra hne
    exact hcon a b hne hab
  have hle : ∀ i, nu i ≤ k := fun i =>
    hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlt : ∀ i, l i < 2 * k := by
    intro i
    have := hle i
    have := i.isLt
    simp only [hl]
    omega
  have hcount := h1 k l hlt hinj
  have hsumL : ∑ i, l i = k + k * (k - 1) / 2 := by
    simp only [hl, Finset.sum_add_distrib, hsum, sum_fin_staircase]
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h1le : nu j ≤ nu i1 := hanti (show i1 ≤ j by rw [Fin.le_iff_val_le_val]; simp [i1]; omega)
  have h0le : nu i1 ≤ nu i0 := hanti (show i0 ≤ i1 by rw [Fin.le_iff_val_le_val]; simp [i0, i1])
  have hsub : ({i0, i1} : Finset (Fin k)) ⊆ univ.filter fun i => k ≤ l i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hv0 : (i0 : ℕ) = 0 := rfl
    have hv1 : (i1 : ℕ) = 1 := rfl
    rcases hx with rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, hv0, hv1] <;> omega
  have hcard : 2 ≤ (univ.filter fun i => k ≤ l i).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by simp [i0, i1, Fin.ext_iff])] at this
  have hmul := Nat.mul_le_mul_left k hcard
  omega
end SchNonHookResidues
end GroundTheory.Heights₂.Heights.RestTerms

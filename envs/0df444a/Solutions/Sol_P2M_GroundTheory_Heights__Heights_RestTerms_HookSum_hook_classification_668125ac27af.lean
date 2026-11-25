-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hook_classification_668125ac27af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:52:28.371136+00:00
-- url     : https://prove2.me/submissions/c4968dfd-c3bf-4da2-aea7-fb4300499bbe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_filter_one_le_le_8f085ebe469f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hookShape_d3ef97502cd4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.HookSum
namespace GroundTheory.Heights₂.Heights.RestTerms.HookSum
theorem _root_.solution {r k : ℕ} (hk : 1 ≤ k) {nu : Fin r → ℕ}
    (hnu : nu ∈ partitionsOf r k) (hh : ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) {l : ℕ}
    (hl : (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card = l) :
    l < r ∧ l < k ∧ hookShape r k l = nu := by
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hnu
  obtain ⟨hsum, hA⟩ := hnu
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := by
    rcases r with _ | r'
    · simp at hsum; omega
    · exact ⟨r', rfl⟩
  set S := (Finset.univ.filter fun i : Fin (r' + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1) with hSdef
  have down : ∀ i j : Fin (r' + 1), ((i : ℕ) ≠ 0 ∧ nu i = 1) → 1 ≤ (j : ℕ) → (j : ℕ) ≤ i →
      ((j : ℕ) ≠ 0 ∧ nu j = 1) := by
    intro i j hi hj1 hji
    have h1 := hA j i (Fin.le_iff_val_le_val.mpr hji)
    have h2 := hh j (by omega)
    exact ⟨by omega, by omega⟩
  have hiff : ∀ i : Fin (r' + 1), ((i : ℕ) ≠ 0 ∧ nu i = 1) ↔ (1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ l) := by
    intro i
    constructor
    · intro hP
      refine ⟨by omega, ?_⟩
      have hsub : (Finset.univ.filter fun j : Fin (r' + 1) => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ i) ⊆ S := by
        intro j hj
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact down i j hP hj.1 hj.2
      have := Finset.card_le_card hsub
      rw [card_filter_one_le_le (r' + 1) i i.isLt] at this
      omega
    · rintro ⟨h1, h2⟩
      by_contra hP
      have hsub : S ⊆ (Finset.univ.filter fun j : Fin (r' + 1) =>
          1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) - 1) := by
        intro j hj
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        refine ⟨by omega, ?_⟩
        by_contra hji
        exact hP (down j i hj (by omega) (by omega))
      have := Finset.card_le_card hsub
      rw [card_filter_one_le_le (r' + 1) ((i : ℕ) - 1) (by omega)] at this
      omega
  have hlr : l < r' + 1 := by
    have hsub : S ⊆ (Finset.univ.filter fun j : Fin (r' + 1) => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ r') := by
      intro j hj
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have := j.isLt
      omega
    have := Finset.card_le_card hsub
    rw [card_filter_one_le_le (r' + 1) r' (by omega)] at this
    omega
  have hval : ∀ i : Fin (r' + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ l then 1 else 0 := by
    intro i hi0
    have h := hiff i
    have h1 := hh i hi0
    split_ifs with hil
    · exact (h.mpr ⟨by omega, hil⟩).2
    · have : ¬ nu i = 1 := fun h' => by have := (h.mp ⟨hi0, h'⟩).2; omega
      omega
  have hsucc : ∀ i : Fin r', nu i.succ = hookShape (r' + 1) k l i.succ := by
    intro i
    rw [hval i.succ (by simp)]
    simp [hookShape]
  have hsumH := sum_hookShape (r' + 1) k l hlr
  rw [Fin.sum_univ_succ] at hsum hsumH
  have h0 : hookShape (r' + 1) k l 0 = k - l := by simp [hookShape]
  simp only [hsucc] at hsum
  rw [h0] at hsumH
  have hnu0 : nu 0 + l = k := by omega
  have hlk : l < k := by
    by_contra hlk
    have hnu00 : nu 0 = 0 := by omega
    have hl1 : 1 ≤ l := by omega
    obtain ⟨i1, hi1⟩ : ∃ i1 : Fin (r' + 1), (i1 : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
    have hP := (hiff i1).mpr ⟨by omega, by omega⟩
    have := hA 0 i1 (Fin.zero_le _)
    omega
  refine ⟨hlr, hlk, ?_⟩
  funext i
  by_cases hi : (i : ℕ) = 0
  · have : i = 0 := Fin.ext hi
    subst this
    rw [h0]
    omega
  · rw [hval i hi]
    simp [hookShape, hi]
end GroundTheory.Heights₂.Heights.RestTerms.HookSum

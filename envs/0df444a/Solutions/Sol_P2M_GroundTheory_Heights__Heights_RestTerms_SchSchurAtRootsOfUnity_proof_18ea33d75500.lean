-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurAtRootsOfUnity_proof_18ea33d75500
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:44.168566+00:00
-- url     : https://prove2.me/submissions/23ab1c78-3231-4962-9e76-a01bfca154ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurAtRootsOfUnity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_schurAtRoots_place_lt_5e36909355b5

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchSchurAtRootsOfUnity
theorem _root_.solution (h1 : SchSchurRowsToK.Statement)
    (h2 : SchSchurEvalMatrix.Statement) (h3 : SchJTMatrixDetAtRoots.Statement) :
    SchSchurAtRootsOfUnity.Statement := by
  intro N r k nu hk hkN hanti hsum
  set nu' : Fin k → ℕ := fun i => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0 with hnu'
  have hplace := schurAtRoots_place_lt nu hanti hsum

  have hanti' : Antitone nu' := by
    intro i j hij
    simp only [hnu']
    by_cases hj : (j : ℕ) < r
    · have hi : (i : ℕ) < r := lt_of_le_of_lt (Fin.le_def.mp hij) hj
      rw [dif_pos hi, dif_pos hj]
      exact hanti (Fin.le_def.mpr (Fin.le_def.mp hij))
    · rw [dif_neg hj]; exact Nat.zero_le _

  have hsum' : ∑ i, nu' i = k := by
    set g : ℕ → ℕ := fun i => if h : i < r then nu ⟨i, h⟩ else 0 with hg
    have e1 : ∑ i, nu' i = ∑ i ∈ range k, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
    have e2 : ∑ i, nu i = ∑ i ∈ range r, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hg, dif_pos i.isLt]
    have hgk : ∀ i, k ≤ i → g i = 0 := by
      intro i hi
      simp only [hg]
      split_ifs with h
      · by_contra hne
        have := hplace ⟨i, h⟩ (Nat.one_le_iff_ne_zero.mpr hne)
        simp at this; omega
      · rfl
    have hgr : ∀ i, r ≤ i → g i = 0 := by
      intro i hi; simp only [hg]; rw [dif_neg (by omega)]
    have e3 : ∑ i ∈ range k, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgk i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    have e4 : ∑ i ∈ range r, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgr i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    rw [e1, e3, ← e4, ← e2, hsum]
  rw [h1 (Fin N) r k nu hanti hsum, h2 N k k _ hk hkN, h3 k nu' hk hanti' hsum']

  have hcond : (∀ i : Fin k, (i : ℕ) ≠ 0 → nu' i ≤ 1) ↔ (∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) := by
    constructor
    · intro H i hi0
      by_cases hz : nu i = 0
      · rw [hz]; exact Nat.zero_le _
      · have hik := hplace i (Nat.one_le_iff_ne_zero.mpr hz)
        have := H ⟨i, hik⟩ hi0
        simp only [hnu', dif_pos i.isLt] at this
        exact this
    · intro H i hi0
      simp only [hnu']
      split_ifs with h
      · exact H ⟨i, h⟩ hi0
      · exact Nat.zero_le _

  have hcard : (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu' i = 1).card =
      (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card := by
    refine Finset.card_bij'
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi
        by_contra h; rw [dif_neg h] at hi; omega⟩)
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hplace i (by omega)⟩) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      obtain ⟨h0, h1⟩ := hi
      split_ifs at h1 with h
      exact ⟨h0, h1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      refine ⟨hi.1, ?_⟩
      rw [dif_pos i.isLt]; exact hi.2
    · intro i hi; rfl
    · intro i hi; rfl
  simp only [hcond, hcard]
end SchSchurAtRootsOfUnity
end GroundTheory.Heights₂.Heights.RestTerms

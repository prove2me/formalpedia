-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurRowsToK_proof_c6e8b5e270b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:11:06.977544+00:00
-- url     : https://prove2.me/submissions/f8bb89b0-8d90-4c18-8c95-64eb70ec4e22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurRowsToK
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_padPartition_94764fcf450d


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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchSchurRowsToK
theorem _root_.solution : SchSchurRowsToK.Statement := by
  intro σ _ _ r k nu hanti hsum
  by_cases hrk : r ≤ k
  · exact (Schur.schur_padPartition σ nu k hrk).symm
  · replace hrk : k < r := Nat.lt_of_not_le hrk
    have hzero : ∀ i : Fin r, k ≤ (i : ℕ) → nu i = 0 := by
      intro i hi
      by_contra hne
      have hpos : 1 ≤ nu i := Nat.one_le_iff_ne_zero.mpr hne
      have h1 : ∑ j ∈ Finset.Iic i, 1 ≤ ∑ j ∈ Finset.Iic i, nu j :=
        Finset.sum_le_sum fun j hj => le_trans hpos (hanti (Finset.mem_Iic.mp hj))
      have h2 : ∑ j ∈ Finset.Iic i, nu j ≤ ∑ j, nu j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h1
      omega
    have heq : nu = Schur.padPartition r
        (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0) := by
      funext i
      simp only [Schur.padPartition]
      by_cases hik : (i : ℕ) < k
      · simp [hik, i.isLt]
      · simp only [hik, dite_false]
        exact hzero i (by omega)
    calc schur σ nu
        = schur σ (Schur.padPartition r
            (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)) :=
          congrArg (schur σ) heq
      _ = _ := Schur.schur_padPartition σ _ r hrk.le
end SchSchurRowsToK
end GroundTheory.Heights₂.Heights.RestTerms

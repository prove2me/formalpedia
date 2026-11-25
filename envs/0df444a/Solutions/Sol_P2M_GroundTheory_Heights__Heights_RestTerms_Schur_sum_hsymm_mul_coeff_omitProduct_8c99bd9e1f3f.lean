-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_sum_hsymm_mul_coeff_omitProduct_8c99bd9e1f3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:34:04.750881+00:00
-- url     : https://prove2.me/submissions/4df75f9f-0631-46c3-ab73-ebbf4904733b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_geomSeries_45d4c16fbfb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_omitProduct_mul_prod_geomSeries_ae43fa042c17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_omitProduct_eq_zero_d1cd08c82e98

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (j : σ) (α : ℕ) :
    ∑ c ∈ range (Fintype.card σ), PowerSeries.coeff c (omitProduct j) *
      (if c ≤ α then hsymm σ ℚ (α - c) else 0) = X j ^ α := by
  have key := congrArg (PowerSeries.coeff α) (omitProduct_mul_prod_geomSeries j)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (omitProduct j) *
      PowerSeries.coeff b (∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ)))] at key
  simp only [coeff_prod_geomSeries] at key
  rw [geomSeries, PowerSeries.coeff_mk] at key
  rw [← key]
  have hbig : ∀ s : Finset ℕ, ∀ f : ℕ → MvPolynomial σ ℚ,
      ∑ c ∈ s, PowerSeries.coeff c (omitProduct j) * f c =
        ∑ c ∈ s.filter (· < Fintype.card σ), PowerSeries.coeff c (omitProduct j) * f c := by
    intro s f
    rw [sum_filter]
    apply sum_congr rfl
    intro c _
    split_ifs with h
    · rfl
    · rw [coeff_omitProduct_eq_zero j c (by omega), zero_mul]
  rw [hbig, hbig (range (α + 1))]
  rw [sum_filter, sum_filter]
  have e1 : ∑ c ∈ range (Fintype.card σ), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0) =
      ∑ c ∈ range (α + 1 + Fintype.card σ), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0) := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro c _ hc
    simp at hc
    simp [show ¬ c < Fintype.card σ by omega]
  have e2 : ∑ c ∈ range (α + 1), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * hsymm σ ℚ (α - c) else 0) =
      ∑ c ∈ range (α + 1 + Fintype.card σ), (if c < Fintype.card σ then
      PowerSeries.coeff c (omitProduct j) * (if c ≤ α then hsymm σ ℚ (α - c) else 0) else 0) := by
    rw [← sum_subset (range_subset_range.mpr (show α + 1 ≤ α + 1 + Fintype.card σ by omega))]
    · apply sum_congr rfl
      intro c hc
      simp at hc
      simp [show c ≤ α by omega]
    · intro c _ hc
      simp at hc
      simp [show ¬ c ≤ α by omega]
  rw [e1, e2]
end GroundTheory.Heights₂.Heights.RestTerms.Schur

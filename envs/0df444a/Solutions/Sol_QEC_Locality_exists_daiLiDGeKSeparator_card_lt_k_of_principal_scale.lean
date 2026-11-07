-- Prove2me | solution 1 for QEC.Locality.exists_daiLiDGeKSeparator_card_lt_k_of_principal_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:33:00.908715+00:00
-- url     : https://prove2.me/submissions/9d52cbb4-bd6e-4784-a876-b61581c3d493

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_daiLiPrincipalFourthRootScale_pow_four
import Theorems.Thm_QEC_Locality_exists_daiLiDGeKSeparator_card_bound
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell k d : ℝ)
    (hk : 0 < k) (hd : 0 < d) (_hDGeK : k ≤ d)
    (hn : 0 < (Fintype.card ι : ℝ))
    (hDistanceDomain : d ≤ Real.sqrt (k * Fintype.card ι))
    (hScale : ell = daiLiPrincipalFourthRootScale k d (Fintype.card ι))
    (hWidth : w = daiLiDGeKGridWidth d ell)
    (hLongCount : (P.longInteractionCount embedding threshold : ℝ) ≤ d / 100)
    (hGridScale : 4 * ell ≤ w) :
    ∃ t : GridTranslation w,
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) < k := by
  have hRatioPos : 0 < k * d ^ 2 / (Fintype.card ι : ℝ) := by
    positivity
  have hEll : 0 < ell := by
    rw [hScale, daiLiPrincipalFourthRootScale]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hRatioPos _)
  have hDGeKSq : d ^ 2 ≤ k * (Fintype.card ι : ℝ) := by
    have hKn : 0 ≤ k * (Fintype.card ι : ℝ) := by positivity
    have hSqrtSq : (Real.sqrt (k * (Fintype.card ι : ℝ))) ^ 2 =
        k * (Fintype.card ι : ℝ) := Real.sq_sqrt hKn
    nlinarith
  have hScalePow : ell ^ 4 = (1 / 100 : ℝ) ^ 4 *
      (k * d ^ 2 / (Fintype.card ι : ℝ)) := by
    rw [hScale]
    exact daiLiPrincipalFourthRootScale_pow_four k d (Fintype.card ι)
      hk.le hn
  have hVertexBudget :
      (32 * ell ^ 2 / w ^ 2) * (Fintype.card ι : ℝ) ≤ (32 / 10000 : ℝ) * k := by
    have hDne : d ≠ 0 := ne_of_gt hd
    have hEllNe : ell ≠ 0 := ne_of_gt hEll
    calc
      (32 * ell ^ 2 / w ^ 2) * (Fintype.card ι : ℝ) =
          32 * 100 ^ 2 * ell ^ 4 * (Fintype.card ι : ℝ) / d ^ 2 := by
        rw [hWidth, daiLiDGeKGridWidth]
        field_simp <;> ring
      _ ≤ (32 / 10000 : ℝ) * k := by
        rw [hScalePow]
        field_simp <;> ring <;> norm_num
  have hRatioLe : k * d ^ 2 / (Fintype.card ι : ℝ) ≤ k ^ 2 := by
    apply (div_le_iff₀ hn).2
    have hMul := mul_le_mul_of_nonneg_left hDGeKSq hk.le
    nlinarith
  have hEllPowLe : ell ^ 4 ≤ (k / 10000 : ℝ) ^ 2 := by
    calc
      ell ^ 4 = (1 / 100 : ℝ) ^ 4 *
          (k * d ^ 2 / (Fintype.card ι : ℝ)) := hScalePow
      _ ≤ (1 / 100 : ℝ) ^ 4 * k ^ 2 := by gcongr
      _ = (k / 10000 : ℝ) ^ 2 := by ring
  have hEllSq : ell ^ 2 ≤ k / 10000 := by
    have hLeft : 0 ≤ ell ^ 2 := sq_nonneg ell
    have hRight : 0 ≤ k / 10000 := by positivity
    nlinarith [sq_nonneg (ell ^ 2 + k / 10000)]
  have hEndpointBudget :
      64 * ell / w * (P.longInteractionCount embedding threshold : ℝ) ≤
        (64 / 10000 : ℝ) * k := by
    have hDne : d ≠ 0 := ne_of_gt hd
    have hEllNe : ell ≠ 0 := ne_of_gt hEll
    calc
      64 * ell / w * (P.longInteractionCount embedding threshold : ℝ) =
          (6400 * ell ^ 2 / d) * (P.longInteractionCount embedding threshold : ℝ) := by
        rw [hWidth, daiLiDGeKGridWidth]
        field_simp <;> ring
      _ ≤ (6400 * ell ^ 2 / d) * (d / 100) := by
        apply mul_le_mul_of_nonneg_left hLongCount
        positivity
      _ = 64 * ell ^ 2 := by
        field_simp <;> ring
      _ ≤ (64 / 10000 : ℝ) * k := by
        calc
          64 * ell ^ 2 ≤ 64 * (k / 10000) := by
            exact mul_le_mul_of_nonneg_left hEllSq (by norm_num)
          _ = (64 / 10000 : ℝ) * k := by ring
  obtain ⟨t, hSeparator⟩ :=
    exists_daiLiDGeKSeparator_card_bound P embedding threshold w ell hEll hGridScale
  refine ⟨t, lt_of_le_of_lt (hSeparator.trans (add_le_add hVertexBudget hEndpointBudget)) ?_⟩
  nlinarith
end QEC.Locality

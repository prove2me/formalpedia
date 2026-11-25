-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPiece_proof_78929f66b0bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:14.566227+00:00
-- url     : https://prove2.me/submissions/630454ef-d7e9-47b7-b289-e7ecb03178c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_realGraphPt_eq_dbcda1298a2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_firstPart_pairPt_6d71954875f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_pairPt_sub_f54c10fbd1af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_le_norm_pairPt_b076ae4cab32
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_zero_be1159debaaa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_graphLin_apply_abc67cdea5c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_normDet_graphLin_eb5fb2a3868a

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
open MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
open AreaGraphPiece
namespace GroundTheory.Heights₂.Heights
namespace AreaGraphPiece
theorem _root_.solution : AreaGraphPiece.Statement := by
  intro k m F A δ t hδ hF
  set L := graphLin A with hLdef
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) ≤ δ := δ.2

  have hsub : ∀ x y, realGraphPt F x - realGraphPt F y - L (x - y) =
      pairPt (0 : EuclideanSpace ℝ (Fin k)) (F x - F y - A (x - y)) := by
    intro x y
    rw [realGraphPt_eq, realGraphPt_eq, hLdef, graphLin_apply, pairPt_sub, pairPt_sub]
    simp
  have hL : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => norm_le_norm_pairPt v (A v)
  have hclose : ∀ x ∈ t, ∀ y ∈ t,
      |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖| ≤ δ * ‖L (x - y)‖ := by
    intro x hx y hy
    calc |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖|
        ≤ ‖realGraphPt F x - realGraphPt F y - L (x - y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖F x - F y - A (x - y)‖ := by rw [hsub, norm_pairPt_zero]
      _ ≤ δ * ‖x - y‖ := hF x hx y hy
      _ ≤ δ * ‖L (x - y)‖ := mul_le_mul_of_nonneg_left (hL _) hδ0

  have himG : realGraphPt F '' t = (fun p => realGraphPt F (firstPart p)) '' (L '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hLdef, graphLin_apply, firstPart_pairPt]
  have hlipG : LipschitzOnWith (1 + δ) (fun p => realGraphPt F (firstPart p)) (L '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [hLdef, graphLin_apply, firstPart_pairPt, dist_eq_norm]
    rw [← graphLin_apply, ← graphLin_apply, ← map_sub, ← hLdef]
    have h := (abs_le.1 (hclose x hx y hy)).2
    push_cast
    linarith

  have himL : L '' t = (fun p => L (firstPart p)) '' (realGraphPt F '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [realGraphPt_eq, firstPart_pairPt]
  have hlipL : LipschitzOnWith (1 - δ)⁻¹ (fun p => L (firstPart p)) (realGraphPt F '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [realGraphPt_eq, firstPart_pairPt, dist_eq_norm]
    rw [← realGraphPt_eq, ← realGraphPt_eq, ← map_sub]
    have h := (abs_le.1 (hclose x hx y hy)).1
    rw [NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one, inv_mul_eq_div,
      le_div_iff₀ (by linarith)]
    nlinarith

  have harea : μH[(k : ℝ)] (L '' t) =
      ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
        μH[(k : ℝ)] t := by
    have h := LinearMap.hausdorffMeasure_image L t
    rw [finrank_euclideanSpace_fin] at h
    rw [h, hLdef, normDet_graphLin]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · calc μH[(k : ℝ)] (realGraphPt F '' t)
        = μH[(k : ℝ)] ((fun p => realGraphPt F (firstPart p)) '' (L '' t)) := by rw [← himG]
      _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (L '' t) :=
          hlipG.hausdorffMeasure_image_le hk
      _ = _ := by rw [harea, ENNReal.rpow_natCast, mul_assoc]
  · have hle : μH[(k : ℝ)] (L '' t) ≤
        (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t) := by
      calc μH[(k : ℝ)] (L '' t)
          = μH[(k : ℝ)] ((fun p => L (firstPart p)) '' (realGraphPt F '' t)) := by rw [← himL]
        _ ≤ (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (realGraphPt F '' t) :=
            hlipL.hausdorffMeasure_image_le hk
        _ = _ := by rw [ENNReal.rpow_natCast]
    have hne : (1 - δ : ℝ≥0) ≠ 0 := (tsub_pos_of_lt hδ).ne'
    calc ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
            μH[(k : ℝ)] t
        = ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (L '' t) := by rw [harea, mul_assoc]
      _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t)) := by gcongr
      _ = μH[(k : ℝ)] (realGraphPt F '' t) := by
          rw [← mul_assoc, ← mul_pow, ← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one,
            one_pow, one_mul]
end AreaGraphPiece
end GroundTheory.Heights₂.Heights

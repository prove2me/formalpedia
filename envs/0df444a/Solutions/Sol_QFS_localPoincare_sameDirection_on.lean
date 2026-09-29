-- Prove2me | solution 1 for QFS.localPoincare_sameDirection_on
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:11:01.834428+00:00
-- url     : https://prove2.me/submissions/c16bcacd-c517-4987-86c9-58938421d2f0

import Theorems.Thm_QFS_lintegral_swap_fibre
import Theorems.Thm_QFS_lintegral_swap_fibre_prime
import Theorems.Thm_QFS_measurable_param_midBall
import Theorems.Thm_QFS_unitBallVol_ne_top


import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_BeyondThePaper
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



namespace QFSNextProof_localPoincare_sameDirection_on

theorem osc_mul_volume_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (s t : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal ((f t - f s) ^ 2) * volume (closedBall (midCentre v ϑ s t) ‖s - t‖)
      ≤ ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
  rw [← setLIntegral_const (closedBall (midCentre v ϑ s t) ‖s - t‖)
    (ENNReal.ofReal ((f t - f s) ^ 2))]
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
  nlinarith [sq_nonneg (f z - f s - (f t - f z)), sq_nonneg (f z - f s + (f t - f z))]

theorem osc_weighted_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ) {α : ℝ}
    (hα : 0 ≤ α) (f : EuclideanSpace ℝ (Fin d) → ℝ) (s t : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(d : ℝ) - α)) *
        unitBallVol d
      ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
        ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by

  have hw : ‖s - t‖ ^ (-(d : ℝ) - α)
      = ‖s - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖s - t‖ ^ d := by
    rcases eq_or_lt_of_le (norm_nonneg (s - t)) with h | h
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        have hne : -(d : ℝ) - α ≠ 0 := by intro hc; linarith
        rw [← h, zero_pow (Nat.ne_of_gt hd), mul_zero, Real.zero_rpow hne]
    · rw [← Real.rpow_natCast ‖s - t‖ d, ← Real.rpow_add h]
      congr 1
      ring
  refine le_trans (le_of_eq ?_)
    (mul_le_mul' (le_refl (ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))))
      (osc_mul_volume_le v ϑ f s t))
  rw [volume_closedBall_eq _ (norm_nonneg _), hw, ENNReal.ofReal_mul (by positivity)]
  ring




end QFSNextProof_localPoincare_sameDirection_on
open QFSNextProof_localPoincare_sameDirection_on

set_option autoImplicit false

theorem solution {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (U : Set (EuclideanSpace ℝ (Fin d))) :
    unitBallVol d * ∫⁻ p in U ×ˢ U,
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst_prime d ϑ α) * unitBallVol d *
          (∫⁻ t in U, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
  set A : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        ENNReal.ofReal (2 * (f z - f p.1) ^ 2) with hAdef
  set B : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        ENNReal.ofReal (2 * (f p.2 - f z) ^ 2) with hBdef
  have hw2m : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) := by fun_prop
  have hHA : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (2 * (f q.2 - f q.1.1) ^ 2) := by fun_prop
  have hHB : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (2 * (f q.1.2 - f q.2) ^ 2) := by fun_prop
  have hGs : ∀ s : EuclideanSpace ℝ (Fin d),
      Measurable fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2) := by intro s; fun_prop
  have hGt : ∀ t : EuclideanSpace ℝ (Fin d),
      Measurable fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2) := by intro t; fun_prop
  have hAm : Measurable A := by
    rw [hAdef]; exact hw2m.mul (QFS.measurable_param_midBall v ϑ hHA)
  have hBm : Measurable B := by
    rw [hBdef]; exact hw2m.mul (QFS.measurable_param_midBall v ϑ hHB)
  have hptwise : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * unitBallVol d ≤ A p + B p := by
    rintro ⟨s, t⟩
    refine le_trans (osc_weighted_le v ϑ hα f s t) (le_of_eq ?_)
    rw [hAdef, hBdef, ← mul_add]
    congr 1
    rw [← lintegral_add_left (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_closedBall fun z _ => ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc unitBallVol d * ∫⁻ p in U ×ˢ U,
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      = ∫⁻ p in U ×ˢ U, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
        rw [← lintegral_const_mul' _ _ QFS.unitBallVol_ne_top]
        exact lintegral_congr fun p => by ring
    _ ≤ ∫⁻ p in U ×ˢ U, (A p + B p) := lintegral_mono hptwise
    _ = (∫⁻ p in U ×ˢ U, A p) + ∫⁻ p in U ×ˢ U, B p := lintegral_add_left hAm _
    _ ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f z - f s) ^ 2) *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst_prime d ϑ α) * unitBallVol d *
          (∫⁻ t in U, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            ENNReal.ofReal (2 * (f t - f z) ^ 2) *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
        refine add_le_add ?_ ?_
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod _ hAm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
          refine lintegral_mono fun s => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (QFS.lintegral_swap_fibre hv hϑ hϑ' hα hd s (hGs s))
        · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod_symm _ hBm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
          refine lintegral_mono fun t => ?_
          exact le_trans (lintegral_mono' Measure.restrict_le_self le_rfl)
            (QFS.lintegral_swap_fibre_prime hv hϑ hϑ' hα hd t (hGt t))
#print axioms solution

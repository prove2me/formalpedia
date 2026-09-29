-- Prove2me | solution 1 for QFS.lintegral_midBall_fibre_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:03:07.525221+00:00
-- url     : https://prove2.me/submissions/0255f455-057c-412a-af29-78cc73e446de

import Theorems.Thm_QFS_norm_sub_le_of_mem_midBall


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



namespace QFSProof_lintegral_midBall_fibre_le_prime

theorem inner_mem_Icc_of_mem_midBall' {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ}
    {s t z : E} (hz : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖) :
    ‖s - t‖ * (3 / Real.sin ϑ - 2) ≤ ⟪v, z - t⟫_ℝ ∧
      ⟪v, z - t⟫_ℝ ≤ ‖s - t‖ * (3 / Real.sin ϑ + 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm, midCentre] at hz
  set q : E := z - (s + (3 * ‖s - t‖ / Real.sin ϑ) • v) with hqdef
  have hq' : ‖q + (s - t)‖ ≤ 2 * ‖s - t‖ := le_trans (norm_add_le _ _) (by linarith)
  have hzt : z - t = (q + (s - t)) + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hinner : ⟪v, z - t⟫_ℝ = ⟪v, q + (s - t)⟫_ℝ + 3 * ‖s - t‖ / Real.sin ϑ := by
    rw [hzt, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hcs : |⟪v, q + (s - t)⟫_ℝ| ≤ ‖q + (s - t)‖ := by
    have := abs_real_inner_le_norm v (q + (s - t))
    rwa [hv, one_mul] at this
  rw [abs_le] at hcs
  have heq : 3 * ‖s - t‖ / Real.sin ϑ = ‖s - t‖ * (3 / Real.sin ϑ) := by ring
  rw [hinner, heq]
  constructor <;> [linarith [hcs.1, hq']; linarith [hcs.2, hq']]

theorem midBall_fibre_subset_closedBall' {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) (t z : E) :
    {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖}
      ⊆ closedBall t (‖z - t‖ / (3 / Real.sin ϑ - 2)) := by
  intro s hs
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hsin1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have h3 : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ := div_nonneg (by linarith) hsin.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by field_simp; ring
    linarith [heq]
  have hden : 0 < 3 / Real.sin ϑ - 2 := by linarith
  obtain ⟨hlow, -⟩ := inner_mem_Icc_of_mem_midBall' (s := s) hv hs
  have hcs : ⟪v, z - t⟫_ℝ ≤ ‖z - t‖ := by
    have := real_inner_le_norm v (z - t)
    rwa [hv, one_mul] at this
  have hdist : dist s t = ‖s - t‖ := dist_eq_norm _ _
  rw [Metric.mem_closedBall, hdist, le_div_iff₀ hden]
  linarith

end QFSProof_lintegral_midBall_fibre_le_prime
open QFSProof_lintegral_midBall_fibre_le_prime

set_option autoImplicit false

theorem solution {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (t z : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
        ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))
      ≤ ENNReal.ofReal (chainConst_prime d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hsin1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have h3 : (3 : ℝ) ≤ 3 / Real.sin ϑ := by
    have hnn : (0 : ℝ) ≤ 3 * (1 - Real.sin ϑ) / Real.sin ϑ := div_nonneg (by linarith) hsin.le
    have heq : 3 + 3 * (1 - Real.sin ϑ) / Real.sin ϑ = 3 / Real.sin ϑ := by field_simp; ring
    linarith [heq]
  have hA : (0 : ℝ) < 2 + 3 / Real.sin ϑ := by linarith
  have hB : (0 : ℝ) < 3 / Real.sin ϑ - 2 := by linarith
  have hsub := midBall_fibre_subset_closedBall' hv hϑ hϑ' t z
  have hmeas : MeasurableSet {s : EuclideanSpace ℝ (Fin d) |
      z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := by
    have h1 : Continuous fun s : EuclideanSpace ℝ (Fin d) => dist z (midCentre v ϑ s t) := by
      unfold midCentre; fun_prop
    have h2 : Continuous fun s : EuclideanSpace ℝ (Fin d) => ‖s - t‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  rcases eq_or_ne z t with rfl | hzt
  · have hball0 : volume (closedBall z (0 : ℝ)) = 0 := by
      rw [volume_closedBall_eq _ le_rfl, zero_pow (Nat.ne_of_gt hd), ENNReal.ofReal_zero, zero_mul]
    have hnull : volume {s : EuclideanSpace ℝ (Fin d) |
        z ∈ closedBall (midCentre v ϑ s z) ‖s - z‖} = 0 := by
      refine measure_mono_null (le_trans hsub (le_of_eq ?_)) hball0
      simp
    rw [setLIntegral_measure_zero _ _ hnull]
    simp
  · have hn : 0 < ‖z - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hzt
    have hexp : -(2 * (d : ℝ)) - α ≤ 0 := by
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have hquot : 0 < ‖z - t‖ / (2 + 3 / Real.sin ϑ) := by positivity
    have hAe : (2 + 3 / Real.sin ϑ) ^ (-(2 * (d : ℝ)) - α)
        = ((2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α))⁻¹ := by
      rw [show -(2 * (d : ℝ)) - α = -(2 * (d : ℝ) + α) from by ring, Real.rpow_neg hA.le]
    have hxe : ‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖z - t‖ ^ ((d : ℕ) : ℝ)
        = ‖z - t‖ ^ (-(d : ℝ) - α) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have hscalar : (‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α) *
        (‖z - t‖ ^ d / (3 / Real.sin ϑ - 2) ^ d)
        = chainConst_prime d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α) := by
      have e1 : (‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)
          = ‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * (2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) := by
        rw [Real.div_rpow hn.le hA.le, hAe, div_eq_mul_inv, inv_inv]
      rw [e1, ← Real.rpow_natCast ‖z - t‖ d, chainConst_prime]
      rw [show ‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * (2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) *
            (‖z - t‖ ^ ((d : ℕ) : ℝ) / (3 / Real.sin ϑ - 2) ^ d)
          = (‖z - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖z - t‖ ^ ((d : ℕ) : ℝ)) *
            ((2 + 3 / Real.sin ϑ) ^ (2 * (d : ℝ) + α) / (3 / Real.sin ϑ - 2) ^ d) from by ring,
        hxe]
      ring
    calc ∫⁻ s in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
            ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α))
        ≤ ∫⁻ _ in {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖},
            ENNReal.ofReal ((‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hmeas] with s hs
          obtain ⟨-, h1⟩ := QFS.norm_sub_le_of_mem_midBall hv hϑ hϑ' hs
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hquot ?_ hexp)
          rw [div_le_iff₀ hA]
          linarith [h1]
      _ = ENNReal.ofReal ((‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) *
            volume {s | z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((‖z - t‖ / (2 + 3 / Real.sin ϑ)) ^ (-(2 * (d : ℝ)) - α)) *
            volume (closedBall t (‖z - t‖ / (3 / Real.sin ϑ - 2))) :=
          mul_le_mul' le_rfl (measure_mono hsub)
      _ = ENNReal.ofReal (chainConst_prime d ϑ α * ‖z - t‖ ^ (-(d : ℝ) - α)) * unitBallVol d := by
          rw [volume_closedBall_eq _ (by positivity), ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hquot.le _), div_pow, hscalar]
#print axioms solution

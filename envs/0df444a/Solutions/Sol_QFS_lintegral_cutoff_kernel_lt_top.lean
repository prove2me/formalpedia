-- Prove2me | solution 1 for QFS.lintegral_cutoff_kernel_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:38:27.561521+00:00
-- url     : https://prove2.me/submissions/98709552-598d-4fd8-86be-1bb39f359632

import Theorems.Thm_QFS_lintegral_compl_ball_rpow_lt_top


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
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}



namespace CutoffProof
theorem lintegral_ball_rpow_lt_top (hd : 0 < d) {r γ : ℝ} (hr : 0 < r)
    (hγ : -(d : ℝ) < γ) :
    ∫⁻ u in ball (0 : EuclideanSpace ℝ (Fin d)) r, ENNReal.ofReal (‖u‖ ^ γ) < ∞ := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    rw [← Module.finrank_pos_iff (R := ℝ), hdim]; exact hd

  have hexp : (-1 : ℝ) < ((d - 1 : ℕ) : ℝ) + γ := by
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have : 1 ≤ d := hd
      push_cast [Nat.cast_sub this]
      ring
    rw [this]; linarith
  have hrad : IntegrableOn
      (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1) • y ^ γ)
      (Ioo 0 r) volume := by
    rw [hdim]
    refine (integrableOn_congr_fun ?_ measurableSet_Ioo).mpr
      ((intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr hexp)
    intro y hy
    have hy0 : (0 : ℝ) < y := hy.1
    change y ^ (d - 1) • y ^ γ = y ^ (((d - 1 : ℕ) : ℝ) + γ)
    rw [smul_eq_mul, ← Real.rpow_natCast y (d - 1), ← Real.rpow_add hy0]
  have hint : IntegrableOn (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ γ) (ball 0 r) volume :=
    (integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ γ) (r := r)).mpr hrad
  have := hint.hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) this
  refine lintegral_congr_ae ?_
  filter_upwards with u
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) γ)]



end CutoffProof
open CutoffProof

set_option autoImplicit false

theorem solution (hd : 0 < d) {δ α : ℝ} (hδ : 0 < δ)
    (hα : 0 < α) (hα2 : α < 2) :
    ∫⁻ u : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)) < ∞ := by
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hcover : (Set.univ : Set (EuclideanSpace ℝ (Fin d)))
      ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) δ ∪
        {u : EuclideanSpace ℝ (Fin d) | δ / 2 < ‖u‖} := by
    intro u _
    by_cases hu : ‖u‖ < δ
    · exact Or.inl (by simpa [Metric.mem_ball, dist_zero_right] using hu)
    · exact Or.inr (by simp only [Set.mem_ofPred_eq]; linarith [not_lt.mp hu])
  have hmin0 : ∀ u : EuclideanSpace ℝ (Fin d), 0 ≤ min (‖u‖ ^ 2 / δ ^ 2) 1 :=
    fun u => le_min (by positivity) zero_le_one
  -- the small scales
  have hsmall : ∀ u : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α))
        ≤ ENNReal.ofReal ((δ ^ 2)⁻¹) *
          ENNReal.ofReal (‖u‖ ^ (2 - (d : ℝ) - α)) := by
    intro u
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases eq_or_ne u 0 with rfl | hu
    · simp only [norm_zero]
      rw [show min ((0 : ℝ) ^ 2 / δ ^ 2) 1 = 0 from by norm_num, zero_mul]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
    · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hpow : ‖u‖ ^ (2 - (d : ℝ) - α) = ‖u‖ ^ (2 : ℕ) * ‖u‖ ^ (-(d : ℝ) - α) := by
        rw [← Real.rpow_natCast ‖u‖ 2, ← Real.rpow_add hn]
        congr 1
        push_cast
        ring
      rw [hpow]
      have h1 : min (‖u‖ ^ 2 / δ ^ 2) 1 ≤ ‖u‖ ^ 2 / δ ^ 2 := min_le_left _ _
      have h2 : (0 : ℝ) ≤ ‖u‖ ^ (-(d : ℝ) - α) := Real.rpow_nonneg hn.le _
      calc min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)
          ≤ (‖u‖ ^ 2 / δ ^ 2) * ‖u‖ ^ (-(d : ℝ) - α) := mul_le_mul_of_nonneg_right h1 h2
        _ = (δ ^ 2)⁻¹ * (‖u‖ ^ (2 : ℕ) * ‖u‖ ^ (-(d : ℝ) - α)) := by
            field_simp
  -- the large scales
  have hlarge : ∀ u : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α))
        ≤ ENNReal.ofReal (‖u‖ ^ (-(d : ℝ) - α)) := by
    intro u
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : min (‖u‖ ^ 2 / δ ^ 2) 1 ≤ 1 := min_le_right _ _
    have h2 : (0 : ℝ) ≤ ‖u‖ ^ (-(d : ℝ) - α) := Real.rpow_nonneg (norm_nonneg u) _
    nlinarith [h1, h2]
  calc ∫⁻ u : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α))
      = ∫⁻ u in Set.univ, ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 *
          ‖u‖ ^ (-(d : ℝ) - α)) := (setLIntegral_univ _).symm
    _ ≤ ∫⁻ u in ball (0 : EuclideanSpace ℝ (Fin d)) δ ∪
          {u : EuclideanSpace ℝ (Fin d) | δ / 2 < ‖u‖},
          ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ u in ball (0 : EuclideanSpace ℝ (Fin d)) δ,
          ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)))
        + ∫⁻ u in {u : EuclideanSpace ℝ (Fin d) | δ / 2 < ‖u‖},
          ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)) :=
        lintegral_union_le _ _ _
    _ < ∞ := by
        refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
        · refine lt_of_le_of_lt (lintegral_mono hsmall) ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lintegral_ball_rpow_lt_top hd hδ (by linarith))
        · refine lt_of_le_of_lt (lintegral_mono hlarge) ?_
          exact QFS.lintegral_compl_ball_rpow_lt_top hd (by linarith) (by linarith)
#print axioms solution

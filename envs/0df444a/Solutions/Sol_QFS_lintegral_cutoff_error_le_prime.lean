-- Prove2me | solution 1 for QFS.lintegral_cutoff_error_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:38:28.585974+00:00
-- url     : https://prove2.me/submissions/1b1f556b-463b-4bf4-9c8c-a0a403ee8bb4

import Theorems.Thm_QFS_lintegral_cutoff_kernel_le
import Theorems.Thm_QFS_lintegral_cutoff_kernel_lt_top


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


set_option autoImplicit false

theorem solution {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ)
    (hα : 0 < α) (hα2 : α < 2)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      k p.1 p.2)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSm : MeasurableSet S) :
    ∫⁻ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (S.indicator (fun z => f z ^ 2) p.2 *
          min (‖p.1 - p.2‖ ^ 2 / δ ^ 2) 1) * k p.1 p.2
      ≤ ENNReal.ofReal Λ *
          (∫⁻ u : EuclideanSpace ℝ (Fin d),
            ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α))) *
          ∫⁻ x in S, ENNReal.ofReal (f x ^ 2) := by
  set Cδ : ℝ≥0∞ := ∫⁻ u : EuclideanSpace ℝ (Fin d),
    ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)) with hCδ
  have hind : ∀ z, 0 ≤ S.indicator (fun z => f z ^ 2) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]; positivity
    · rw [Set.indicator_of_notMem hz]
  have hmeasint : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (S.indicator (fun z => f z ^ 2) p.2 *
        min (‖p.1 - p.2‖ ^ 2 / δ ^ 2) 1) * k p.1 p.2 := by
    refine Measurable.mul ?_ hkm
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ (by fun_prop))
    exact ((hf.pow_const 2).indicator hSm).comp measurable_snd
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hmeasint.aemeasurable]
  have hstep : ∀ y : EuclideanSpace ℝ (Fin d),
      ∫⁻ x, ENNReal.ofReal (S.indicator (fun z => f z ^ 2) y *
          min (‖x - y‖ ^ 2 / δ ^ 2) 1) * k x y
        ≤ ENNReal.ofReal (S.indicator (fun z => f z ^ 2) y) * (ENNReal.ofReal Λ * Cδ) := by
    intro y
    have hrw : ∀ x, ENNReal.ofReal (S.indicator (fun z => f z ^ 2) y *
        min (‖x - y‖ ^ 2 / δ ^ 2) 1) * k x y
        = ENNReal.ofReal (S.indicator (fun z => f z ^ 2) y) *
          (ENNReal.ofReal (min (‖y - x‖ ^ 2 / δ ^ 2) 1) * k y x) := by
      intro x
      rw [ENNReal.ofReal_mul (hind y), norm_sub_rev x y, hk.symm x y]
      ring
    rw [lintegral_congr hrw, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (QFS.lintegral_cutoff_kernel_le hk hδ y)
  calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal (S.indicator (fun z => f z ^ 2) y *
        min (‖x - y‖ ^ 2 / δ ^ 2) 1) * k x y
      ≤ ∫⁻ y, ENNReal.ofReal (S.indicator (fun z => f z ^ 2) y) *
          (ENNReal.ofReal Λ * Cδ) := lintegral_mono hstep
    _ = (∫⁻ y, ENNReal.ofReal (S.indicator (fun z => f z ^ 2) y)) *
          (ENNReal.ofReal Λ * Cδ) :=
        lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (by rw [hCδ]; exact (QFS.lintegral_cutoff_kernel_lt_top hd hδ hα hα2).ne))
    _ = ENNReal.ofReal Λ * Cδ * ∫⁻ x in S, ENNReal.ofReal (f x ^ 2) := by
        have hindeq : ∀ x, ENNReal.ofReal (S.indicator (fun z => f z ^ 2) x)
            = S.indicator (fun z => ENNReal.ofReal (f z ^ 2)) x := by
          intro x
          by_cases hx : x ∈ S
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
        rw [lintegral_congr hindeq, lintegral_indicator hSm]
        ring
#print axioms solution

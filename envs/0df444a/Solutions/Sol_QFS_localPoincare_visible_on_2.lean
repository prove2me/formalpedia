-- Prove2me | solution 2 for QFS.localPoincare_visible_on
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:11:02.466148+00:00
-- url     : https://prove2.me/submissions/7101f09c-9bc5-4b52-b7b1-9ed5a9e5e7ff

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



namespace QFSNextProof_localPoincare_visible_on

theorem osc_weighted_le_visible' {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ) {α c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {s t : EuclideanSpace ℝ (Fin d)} (hst : s ≠ t)
    (hU : ENNReal.ofReal (c₀ * ‖s - t‖ ^ d) ≤
      volume (U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖)) :
    ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(d : ℝ) - α)) *
        ENNReal.ofReal c₀
      ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
        ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
          U.indicator (fun z =>
            ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z := by
  have hr : 0 < ‖s - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hst
  have hw : ‖s - t‖ ^ (-(d : ℝ) - α)
      = ‖s - t‖ ^ (-(2 * (d : ℝ)) - α) * ‖s - t‖ ^ d := by
    rw [← Real.rpow_natCast ‖s - t‖ d, ← Real.rpow_add hr]
    congr 1
    ring
  have heq : ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
        U.indicator (fun z =>
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z
      = ∫⁻ z in U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
    rw [lintegral_indicator hUm, Measure.restrict_restrict hUm]
  have hpt : ENNReal.ofReal ((f t - f s) ^ 2) *
        volume (U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖)
      ≤ ∫⁻ z in U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
    rw [← setLIntegral_const (U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖)
      (ENNReal.ofReal ((f t - f s) ^ 2))]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (f z - f s - (f t - f z)), sq_nonneg (f z - f s + (f t - f z))]
  calc ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(d : ℝ) - α)) *
        ENNReal.ofReal c₀
      = ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          (ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (c₀ * ‖s - t‖ ^ d)) := by
        rw [hw, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc₀]
        ring
    _ ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          (ENNReal.ofReal ((f t - f s) ^ 2) *
            volume (U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hU)
    _ ≤ ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          ∫⁻ z in U ∩ closedBall (midCentre v ϑ s t) ‖s - t‖,
            ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) :=
        mul_le_mul' le_rfl hpt
    _ = ENNReal.ofReal (‖s - t‖ ^ (-(2 * (d : ℝ)) - α)) *
          ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
            U.indicator (fun z =>
              ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z := by
        rw [heq]




end QFSNextProof_localPoincare_visible_on
open QFSNextProof_localPoincare_visible_on

set_option autoImplicit false

theorem solution {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α c₀ : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    (hc₀ : 0 ≤ c₀) {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    {P : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))} (hPm : MeasurableSet P)
    (hU : ∀ p ∈ P, p.1 ≠ p.2 → ENNReal.ofReal (c₀ * ‖p.1 - p.2‖ ^ d) ≤
      volume (U ∩ closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) :
    ENNReal.ofReal c₀ * ∫⁻ p in P,
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst_prime d ϑ α) * unitBallVol d *
          (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
  set A : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        U.indicator (fun z => ENNReal.ofReal (2 * (f z - f p.1) ^ 2)) z with hAdef
  set B : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) *
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖,
        U.indicator (fun z => ENNReal.ofReal (2 * (f p.2 - f z) ^ 2)) z with hBdef
  have hw2m : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(2 * (d : ℝ)) - α)) := by fun_prop
  have hUsnd : MeasurableSet {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) | q.2 ∈ U} := hUm.preimage measurable_snd
  have hHA : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) =>
      U.indicator (fun z => ENNReal.ofReal (2 * (f z - f q.1.1) ^ 2)) q.2 := by
    have hEq : (fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) =>
          U.indicator (fun z => ENNReal.ofReal (2 * (f z - f q.1.1) ^ 2)) q.2)
        = {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) | q.2 ∈ U}.indicator
            (fun q => ENNReal.ofReal (2 * (f q.2 - f q.1.1) ^ 2)) := by
      funext q
      by_cases hq : q.2 ∈ U
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ {q | q.2 ∈ U} from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ {q | q.2 ∈ U} from hq)]
    rw [hEq]
    exact Measurable.indicator (by fun_prop) hUsnd
  have hHB : Measurable fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) =>
      U.indicator (fun z => ENNReal.ofReal (2 * (f q.1.2 - f z) ^ 2)) q.2 := by
    have hEq : (fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) =>
          U.indicator (fun z => ENNReal.ofReal (2 * (f q.1.2 - f z) ^ 2)) q.2)
        = {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) | q.2 ∈ U}.indicator
            (fun q => ENNReal.ofReal (2 * (f q.1.2 - f q.2) ^ 2)) := by
      funext q
      by_cases hq : q.2 ∈ U
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ {q | q.2 ∈ U} from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ {q | q.2 ∈ U} from hq)]
    rw [hEq]
    exact Measurable.indicator (by fun_prop) hUsnd
  have hGs : ∀ s : EuclideanSpace ℝ (Fin d),
      Measurable (U.indicator fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) := by
    intro s; exact Measurable.indicator (by fun_prop) hUm
  have hGt : ∀ t : EuclideanSpace ℝ (Fin d),
      Measurable (U.indicator fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) := by
    intro t; exact Measurable.indicator (by fun_prop) hUm
  have hAm : Measurable A := by
    rw [hAdef]; exact hw2m.mul (QFS.measurable_param_midBall v ϑ hHA)
  have hBm : Measurable B := by
    rw [hBdef]; exact hw2m.mul (QFS.measurable_param_midBall v ϑ hHB)

  have hptwise : ∀ p ∈ P,
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
        ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * ENNReal.ofReal c₀
        ≤ A p + B p := by
    rintro ⟨s, t⟩ hp
    by_cases hst : s = t
    · subst hst
      simp only [sub_self, norm_zero]
      rw [Real.zero_rpow (by
        have : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
        intro hc; linarith), ENNReal.ofReal_zero]
      simp
    · have hsplit : ∀ z : EuclideanSpace ℝ (Fin d),
          U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z
            = U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z
              + U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z := by
        intro z
        by_cases hz : z ∈ U
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
            Set.indicator_of_notMem hz, add_zero]
      have hsum : ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
            U.indicator (fun z =>
              ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2)) z
          = (∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
              U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z)
            + ∫⁻ z in closedBall (midCentre v ϑ s t) ‖s - t‖,
              U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z := by
        rw [← lintegral_add_left (hGs s)]
        exact lintegral_congr fun z => hsplit z
      refine le_trans (osc_weighted_le_visible' v ϑ hc₀ hUm f hst (hU (s, t) hp hst))
        (le_of_eq ?_)
      rw [hAdef, hBdef, ← mul_add]
      exact congrArg _ hsum
  calc ENNReal.ofReal c₀ * ∫⁻ p in P,
          ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α))
      = ∫⁻ p in P, ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) * ENNReal.ofReal c₀ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun p => by ring
    _ ≤ ∫⁻ p in P, (A p + B p) := setLIntegral_mono' hPm hptwise
    _ ≤ ∫⁻ p, (A p + B p) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = (∫⁻ p, A p) + ∫⁻ p, B p := lintegral_add_left hAm _
    _ ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (∫⁻ s, ∫⁻ z in {z | z - s ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f z - f s) ^ 2)) z *
              ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
        + ENNReal.ofReal (chainConst_prime d ϑ α) * unitBallVol d *
          (∫⁻ t, ∫⁻ z in {z | z - t ∈ cone v ϑ},
            U.indicator (fun z => ENNReal.ofReal (2 * (f t - f z) ^ 2)) z *
              ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α))) := by
        refine add_le_add ?_ ?_
        · rw [Measure.volume_eq_prod, lintegral_prod _ hAm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
          exact lintegral_mono fun s => QFS.lintegral_swap_fibre hv hϑ hϑ' hα hd s (hGs s)
        · rw [Measure.volume_eq_prod, lintegral_prod_symm _ hBm.aemeasurable,
            ← lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top QFS.unitBallVol_ne_top)]
          exact lintegral_mono fun t => QFS.lintegral_swap_fibre_prime hv hϑ hϑ' hα hd t (hGt t)
#print axioms solution

-- Prove2me | solution 1 for QFS.formHs_le_form_of_commonDirection_on
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:18:29.895165+00:00
-- url     : https://prove2.me/submissions/ceb2551d-9095-4ee0-be83-ae9c0dff76cf

import Theorems.Thm_QFS_jumpKernel_le_of_mem_coneAt
import Theorems.Thm_QFS_localPoincare_sameDirection_on


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


set_option autoImplicit false

theorem solution {d : ℕ} {v : EuclideanSpace ℝ (Fin d)}
    (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α) (hd : 0 < d)
    {Γ : Configuration (EuclideanSpace ℝ (Fin d))} {Λ : ℝ}
    {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    (hcommon : ∀ x ∈ U, cone v ϑ ⊆ (Γ x).carrier)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hkm : Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * k p.1 p.2) :
    unitBallVol d * ∫⁻ p in U ×ˢ U,
        ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
      ≤ ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst_prime d ϑ α)) *
          unitBallVol d * form Set.univ k f := by
  have hΛ : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hk.one_le
  have hform : form Set.univ k f
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f y - f x) ^ 2) * k x y := by
    rw [form, Set.univ_prod_univ, setLIntegral_univ, Measure.volume_eq_prod,
      lintegral_prod _ hkm.aemeasurable]
  have hconeMeas : ∀ x : EuclideanSpace ℝ (Fin d),
      MeasurableSet {y : EuclideanSpace ℝ (Fin d) | y - x ∈ cone v ϑ} := fun x =>
    ((isOpen_cone v ϑ).preimage (by fun_prop)).measurableSet
  have hterm : ∀ (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ x y, (g x y) ^ 2 = (f y - f x) ^ 2) →
      (∫⁻ x in U, ∫⁻ y in {y | y - x ∈ cone v ϑ},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)))
        ≤ ENNReal.ofReal (2 * Λ) * form Set.univ k f := by
    intro g hg
    rw [hform, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (lintegral_mono_ae ?_) (lintegral_mono' Measure.restrict_le_self le_rfl)
    filter_upwards [ae_restrict_mem hUm] with x hxU
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ y in {y | y - x ∈ cone v ϑ},
          ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
        ≤ ∫⁻ y in {y | y - x ∈ cone v ϑ},
            ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hconeMeas x)] with y hyc
          have hmem : y ∈ coneAt Γ x := hcommon x hxU hyc
          have hjk : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)) ≤ ENNReal.ofReal Λ * k x y := by
            have h0 : ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α)) = jumpKernel d α x y := by
              rw [jumpKernel, norm_sub_rev]
            rw [h0]; exact QFS.jumpKernel_le_of_mem_coneAt hk hmem
          calc ENNReal.ofReal (2 * (g x y) ^ 2) * ENNReal.ofReal (‖y - x‖ ^ (-(d : ℝ) - α))
              ≤ ENNReal.ofReal (2 * (f y - f x) ^ 2) * (ENNReal.ofReal Λ * k x y) := by
                rw [hg]; exact mul_le_mul' le_rfl hjk
            _ = ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
                ring
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 * Λ) * (ENNReal.ofReal ((f y - f x) ^ 2) * k x y) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
  have hlhs : ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((f p.2 - f p.1) ^ 2) * jumpKernel d α p.1 p.2
        = ENNReal.ofReal ((f p.2 - f p.1) ^ 2) *
          ENNReal.ofReal (‖p.1 - p.2‖ ^ (-(d : ℝ) - α)) := fun p => rfl
  rw [lintegral_congr hlhs]
  refine le_trans (QFS.localPoincare_sameDirection_on hv hϑ hϑ' hα hd hf U) ?_
  have hA := hterm (fun x y => f y - f x) (fun x y => rfl)
  have hB := hterm (fun x y => f x - f y) (fun x y => by ring)
  calc ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
        (∫⁻ s in U, ∫⁻ z in {z | z - s ∈ cone v ϑ},
          ENNReal.ofReal (2 * (f z - f s) ^ 2) * ENNReal.ofReal (‖z - s‖ ^ (-(d : ℝ) - α)))
      + ENNReal.ofReal (chainConst_prime d ϑ α) * unitBallVol d *
        (∫⁻ t in U, ∫⁻ z in {z | z - t ∈ cone v ϑ},
          ENNReal.ofReal (2 * (f t - f z) ^ 2) * ENNReal.ofReal (‖z - t‖ ^ (-(d : ℝ) - α)))
      ≤ ENNReal.ofReal (chainConst d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f)
        + ENNReal.ofReal (chainConst_prime d ϑ α) * unitBallVol d *
          (ENNReal.ofReal (2 * Λ) * form Set.univ k f) :=
        add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB)
    _ = ENNReal.ofReal (2 * Λ) *
          (ENNReal.ofReal (chainConst d ϑ α) + ENNReal.ofReal (chainConst_prime d ϑ α)) *
          unitBallVol d * form Set.univ k f := by ring
#print axioms solution

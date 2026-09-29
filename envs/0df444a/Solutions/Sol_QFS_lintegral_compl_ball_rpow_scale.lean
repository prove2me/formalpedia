-- Prove2me | solution 1 for QFS.lintegral_compl_ball_rpow_scale
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:09.194416+00:00
-- url     : https://prove2.me/submissions/1e858f10-5999-44b8-b562-44fad61879be




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

theorem solution {α r : ℝ} (hr : 0 < r) :
    ∫⁻ u in {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖},
        ENNReal.ofReal (‖u‖ ^ (-(d : ℝ) - α))
      = ENNReal.ofReal (r ^ (-α)) *
        ∫⁻ u in {u : EuclideanSpace ℝ (Fin d) | 1 < ‖u‖},
          ENNReal.ofReal (‖u‖ ^ (-(d : ℝ) - α)) := by
  set γ : ℝ := -(d : ℝ) - α with hγ
  have hmr : MeasurableSet {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hm1 : MeasurableSet {u : EuclideanSpace ℝ (Fin d) | 1 < ‖u‖} :=
    measurableSet_lt measurable_const measurable_norm
  set G : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun u =>
    {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖}.indicator
      (fun u => ENNReal.ofReal (‖u‖ ^ γ)) u with hG
  set F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun u =>
    {u : EuclideanSpace ℝ (Fin d) | 1 < ‖u‖}.indicator
      (fun u => ENNReal.ofReal (‖u‖ ^ γ)) u with hF
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)).indicator hmr
  -- the dilation identity
  have hdil : ∫⁻ z : EuclideanSpace ℝ (Fin d), G (r • z)
      = ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ z : EuclideanSpace ℝ (Fin d), G z := by
    have hmap := Measure.map_addHaar_smul
      (volume : Measure (EuclideanSpace ℝ (Fin d))) (ne_of_gt hr)
    have hlm := lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (f := G) (g := fun z : EuclideanSpace ℝ (Fin d) => r • z) hGm (by fun_prop)
    rw [hmap] at hlm
    rw [← hlm, lintegral_smul_measure]
    congr 1
    simp [abs_of_pos, hr, finrank_euclideanSpace]
  -- the integrand after the dilation
  have hpt : ∀ z : EuclideanSpace ℝ (Fin d),
      G (r • z) = ENNReal.ofReal (r ^ γ) * F z := by
    intro z
    have hnorm : ‖r • z‖ = r * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp only [hG, hF]
    by_cases hz : (1:ℝ) < ‖z‖
    · have hrz : r • z ∈ {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖} := by
        rw [Set.mem_ofPred_eq, hnorm]
        nlinarith
      rw [Set.indicator_of_mem hrz,
        Set.indicator_of_mem (show z ∈ {u : EuclideanSpace ℝ (Fin d) | 1 < ‖u‖} from hz),
        hnorm, Real.mul_rpow hr.le (norm_nonneg _), ENNReal.ofReal_mul (by positivity)]
    · have hrz : r • z ∉ {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖} := by
        rw [Set.mem_ofPred_eq, hnorm]
        push Not at hz ⊢
        nlinarith [norm_nonneg z]
      rw [Set.indicator_of_notMem hrz,
        Set.indicator_of_notMem (show z ∉ {u : EuclideanSpace ℝ (Fin d) | 1 < ‖u‖} from hz),
        mul_zero]
  have hcalc : ∫⁻ z : EuclideanSpace ℝ (Fin d), G (r • z)
      = ENNReal.ofReal (r ^ γ) * ∫⁻ z : EuclideanSpace ℝ (Fin d), F z := by
    rw [show (fun z : EuclideanSpace ℝ (Fin d) => G (r • z))
        = fun z => ENNReal.ofReal (r ^ γ) * F z from funext hpt,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_indicator hmr, ← lintegral_indicator hm1, ← hG, ← hF]
  have hrd : (0:ℝ) < r ^ d := by positivity
  have := hdil.symm.trans hcalc
  -- solve for `∫ G`
  have hne0 : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hnetop : ENNReal.ofReal ((r ^ d)⁻¹) ≠ ∞ := ENNReal.ofReal_ne_top
  have hsolve : ∫⁻ z : EuclideanSpace ℝ (Fin d), G z
      = ENNReal.ofReal (r ^ d) * (ENNReal.ofReal (r ^ γ) *
        ∫⁻ z : EuclideanSpace ℝ (Fin d), F z) := by
    rw [← this, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ (ne_of_gt hrd), ENNReal.ofReal_one, one_mul]
  rw [hsolve, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [← Real.rpow_natCast r d, ← Real.rpow_add hr, hγ]
  congr 1
  ring
#print axioms solution

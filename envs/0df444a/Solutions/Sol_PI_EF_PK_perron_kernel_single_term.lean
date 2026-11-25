-- Prove2me | solution 1 for PI.EF.PK.perron_kernel_single_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:55.234772+00:00
-- url     : https://prove2.me/submissions/0631ff70-242d-4102-a998-a046f90278df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelB
import Theorems.Thm_PI_EF_PK_line_bound_small
import Theorems.Thm_PI_EF_PK_line_bound_neg
import Theorems.Thm_PI_EF_PK_line_bound_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution : PerronKernel := by
  intro y c T hy hc hT
  obtain ⟨l, hl⟩ : ∃ l, l = Real.log y := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = y ^ c := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = ∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / (2 * π) := ⟨_, rfl⟩
  have hpi : 3 < π := Real.pi_gt_three
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r * (2 * π) = 1 := by rw [hr]; field_simp
  have hEe : E = Real.exp (l * c) := by rw [hE, hl]; exact Real.rpow_def_of_pos hy c
  have hE0 : 0 < E := by rw [hEe]; exact Real.exp_pos _
  have hK : perronK y c T = (r : ℂ) * J := by
    unfold perronK
    rw [hr, hJ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [ker]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le, ← hl]
  rw [← hl, ← hE, hK]
  obtain ⟨X, hX⟩ : ∃ X, X = ‖(r : ℂ) * J - (if 1 ≤ y then 1 else 0)‖ := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]

  have hb : T * |l| * X ≤ E := by
    rcases lt_trichotomy l 0 with hneg | hzero | hpos
    · have hy1 : y < 1 := (Real.log_neg_iff hy).mp (hl ▸ hneg)
      have h1 := line_bound_neg l c T hneg hc hT
      rw [← hJ, ← hEe] at h1
      have hXe : X = r * ‖J‖ := by
        rw [hX, if_neg (not_le.mpr hy1), sub_zero, norm_mul, hnr]
      rw [hXe, abs_of_neg hneg]
      have hl' : 0 < -l := by linarith
      calc T * -l * (r * ‖J‖) ≤ T * -l * (r * (2 * (E / (-l) / T))) := by gcongr
        _ = (r * 2) * E := by
            have hl0 : l ≠ 0 := hneg.ne
            field_simp
        _ ≤ 1 * E := by
            gcongr
            nlinarith
        _ = E := one_mul _
    · rw [hzero]; simp [hE0.le]
    · have hy1 : 1 ≤ y := ((Real.log_pos_iff hy.le).mp (hl ▸ hpos)).le
      have h1 := line_bound_pos l c T hpos hc hT
      rw [← hJ, ← hEe] at h1
      have hXe : X = r * ‖J - 2 * π‖ := by
        rw [hX, if_pos hy1, ← hnr, ← norm_mul, hnr]
        congr 1
        have : (r : ℂ) * (2 * π) = 1 := by exact_mod_cast hr1
        linear_combination this
      rw [hXe, abs_of_pos hpos]
      calc T * l * (r * ‖J - 2 * π‖) ≤ T * l * (r * (2 * (E / l / T))) := by gcongr
        _ = (r * 2) * E := by field_simp
        _ ≤ 1 * E := by
            gcongr
            nlinarith
        _ = E := one_mul _
  refine ⟨?_, hb⟩
  by_cases hsm : T * |l| ≤ 1
  · have h1 := line_bound_small l c T hc hT
    rw [← hJ, ← hEe] at h1
    have hind : ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ ≤ E := by
      split_ifs with hy1
      · rw [norm_one, hE]
        exact Real.one_le_rpow hy1 hc.le
      · rw [norm_zero]; exact hE0.le
    have h2 : r * ‖J‖ ≤ E := by
      calc r * ‖J‖ ≤ r * (E * (π + |l| * (2 * T))) := by gcongr
        _ ≤ r * (E * (π + 2)) := by
            gcongr
            nlinarith
        _ ≤ r * (E * (2 * π)) := by
            gcongr
            linarith
        _ = (r * (2 * π)) * E := by ring
        _ = E := by rw [hr1, one_mul]
    calc X ≤ ‖(r : ℂ) * J‖ + ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ := by rw [hX]; exact norm_sub_le _ _
      _ = r * ‖J‖ + ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ := by rw [norm_mul, hnr]
      _ ≤ 2 * E := by linarith
  · rw [not_le] at hsm
    nlinarith
end PI.EF.PK

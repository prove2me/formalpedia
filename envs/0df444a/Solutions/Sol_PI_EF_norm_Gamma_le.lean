-- Prove2me | solution 1 for PI.EF.norm_Gamma_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:51.421198+00:00
-- url     : https://prove2.me/submissions/81aa4050-c9dc-457e-a230-2677b38bc0a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Set
namespace PI.EF
theorem _root_.solution {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp
end PI.EF

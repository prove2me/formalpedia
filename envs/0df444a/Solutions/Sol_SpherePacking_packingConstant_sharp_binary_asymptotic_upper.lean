-- Prove2me | solution 1 for SpherePacking.packingConstant_sharp_binary_asymptotic_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/b7e236c3-ce67-4867-98e7-3f358af142b2

import Theorems.Thm_CohnElkies_exists_manuscriptBinaryIsLittleO
import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_packingConstant_le_radial_linear_program

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
theorem _root_.solution :
    ∃ e : ℕ → ℝ,
      Tendsto e atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        packingConstant n ≤
          ENNReal.ofReal
            ((2 : ℝ) ^
              (-(CohnElkies.criticalBinaryExponent + e n) * (n : ℝ))) := by
  obtain ⟨e, he, hformula⟩ := CohnElkies.exists_manuscriptBinaryIsLittleO
  refine ⟨e, (Asymptotics.isLittleO_one_iff ℝ).mp he, ?_⟩
  filter_upwards [hformula, eventually_gt_atTop (0 : ℕ)] with n hformula' hn
  rw [← hformula']
  exact packingConstant_le_radial_linear_program hn
end SpherePacking

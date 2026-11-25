-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.leviForm_fsMetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:40:03.485413+00:00
-- url     : https://prove2.me/submissions/59b0048d-57a6-4967-9832-6b8009dd418c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_smul_I
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fsLp_normSq_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_hess_logFs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_inner_sq_add_inner_I_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    leviForm (fun z => Real.log ((fsMetric ι).ρ z)) z w =
      (‖fsLp ι w‖ ^ 2 * ‖fsLp ι z‖ ^ 2 - ‖inner ℂ (fsLp ι z) (fsLp ι w)‖ ^ 2) /
        (2 * (‖fsLp ι z‖ ^ 2) ^ 2) := by
  change leviForm (fun z => Real.log ‖fsLp ι z‖) z w = _
  unfold leviForm
  rw [hess_logFs hz, hess_logFs hz, fsLp_smul_I, norm_smul, Complex.norm_I, one_mul,
    ← inner_sq_add_inner_I_sq]
  have h0 := fsLp_normSq_ne_zero hz
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.Geo

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paD_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:33:58.440558+00:00
-- url     : https://prove2.me/submissions/4aa7fd7c-3884-4095-8803-db570e3b2216

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paD_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (α : ι →₀ ℕ) (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}
    (h : ContDiff ℂ (⊤ : ℕ∞) H) : paD α (a • H) = a * paD α H := by
  exact FPw.paD_smul α a h
end ReciprocityTheory.ChartRestriction.G.I2

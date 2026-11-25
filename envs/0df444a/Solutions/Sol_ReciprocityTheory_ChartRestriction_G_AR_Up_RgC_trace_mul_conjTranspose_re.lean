-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgC.trace_mul_conjTranspose_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:33:59.962747+00:00
-- url     : https://prove2.me/submissions/4900044a-211c-43f3-bf1e-513e67e5dd1b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
theorem _root_.solution {r s : ℕ} (B : Matrix (Fin r) (Fin s) ℂ) :
    (B * Bᴴ).trace.re = ∑ a, ∑ b, Complex.normSq (B a b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

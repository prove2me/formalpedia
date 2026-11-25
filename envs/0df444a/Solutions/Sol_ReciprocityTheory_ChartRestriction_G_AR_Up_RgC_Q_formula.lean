-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgC.Q_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:11:42.151928+00:00
-- url     : https://prove2.me/submissions/2c5f3f1b-f3a8-44c4-a624-cc808a538f5c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgC_trace_mul_conjTranspose_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
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
theorem _root_.solution {r s : ℕ} (Z : Matrix (Fin r) (Fin s) ℂ) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((1 - Z * Zᴴ) * (yᴴ * y)).trace.re =
      (yᴴ * y).trace.re - ∑ a, ∑ b, Complex.normSq ((y * Z) a b) := by
  rw [← trace_mul_conjTranspose_re, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re]
  congr 2
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_trace_mct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:43.120358+00:00
-- url     : https://prove2.me/submissions/f1336143-db24-423d-95f3-f1ae195d7634

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    (trace (X * Xᴴ)).re = sumBdFsq X := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, sumBdFsq, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]
end ReciprocityTheory.ChartRestriction.G.AR.Up

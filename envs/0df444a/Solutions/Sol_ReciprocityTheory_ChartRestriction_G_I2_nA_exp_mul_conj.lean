-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_exp_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:02.104931+00:00
-- url     : https://prove2.me/submissions/9c770b18-0ebf-42ae-bc6e-357f81ff1e83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {ι : Type} [Fintype ι]
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (z : ℂ) : cexp z * (starRingEnd ℂ) (cexp z) = ((Real.exp (2 * z.re) : ℝ) : ℂ) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.add_conj, Complex.ofReal_exp]
end ReciprocityTheory.ChartRestriction.G.I2

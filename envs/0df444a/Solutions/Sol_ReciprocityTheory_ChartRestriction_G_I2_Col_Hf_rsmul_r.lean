-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_rsmul_r
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:06.032446+00:00
-- url     : https://prove2.me/submissions/53c4724a-30c8-4107-bc02-795a1ec2f002

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement

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
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (r : ℝ) (v w : EuclideanSpace ℂ ι) : Hf v (r • w) = r * Hf v w := by
  simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
end ReciprocityTheory.ChartRestriction.G.I2.Col

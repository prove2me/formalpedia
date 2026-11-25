-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.jof_Hf_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:11:09.466801+00:00
-- url     : https://prove2.me/submissions/bc9b0a91-bcd5-4d3f-bdaf-6e511db4121c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : star (Hf v w) = Hf w v := by
  simp only [Hf, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.star_def, mul_comm]
end ReciprocityTheory.ChartRestriction.G.I2

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_Hf_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:01.462841+00:00
-- url     : https://prove2.me/submissions/500decfc-0d08-415e-bd8d-c925158d4327

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (v w : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf v w) = Hf w v := by
  simp [Hf, map_sum, mul_comm]
end ReciprocityTheory.ChartRestriction.G.I2

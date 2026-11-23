-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:07.280697+00:00
-- url     : https://prove2.me/submissions/eea71bdb-7220-4f6f-8d86-409e99d95a1a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_Hf_conj

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
theorem _root_.solution (v w : Fin n → EuclideanSpace ℂ ι) : (starRingEnd ℂ) (HC v w) = HC w v := by
  simp [HC, map_sum, nA_Hf_conj]
end ReciprocityTheory.ChartRestriction.G.I2

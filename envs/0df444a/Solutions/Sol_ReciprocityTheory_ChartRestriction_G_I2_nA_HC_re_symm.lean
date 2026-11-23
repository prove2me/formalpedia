-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_HC_re_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:45.042812+00:00
-- url     : https://prove2.me/submissions/a03b4c80-1b14-4275-9571-57999db1a30a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_HC_conj

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
theorem _root_.solution (v w : Fin n → EuclideanSpace ℂ ι) : (HC w v).re = (HC v w).re := by
  rw [← nA_HC_conj v w, Complex.conj_re]
end ReciprocityTheory.ChartRestriction.G.I2

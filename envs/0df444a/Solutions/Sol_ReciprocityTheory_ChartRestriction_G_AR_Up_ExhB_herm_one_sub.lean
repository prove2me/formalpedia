-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.herm_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:08.746282+00:00
-- url     : https://prove2.me/submissions/89d44b65-c7ff-469a-932d-ff7c7899ab7c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
theorem _root_.solution {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) : (1 - Z * Zᴴ).IsHermitian :=
  isHermitian_one.sub (isHermitian_mul_conjTranspose_self Z)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB

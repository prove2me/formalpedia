-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_hm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:50.379127+00:00
-- url     : https://prove2.me/submissions/6c26dc48-3d7a-4f44-9e47-4fdf43dc6cc9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (σ J)
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (e f : ι → K) (l m : K) : tor σ J e f l m = hm σ J e f !![l, 0; 0, m] := by
  ext i j
  simp [tor, hm, vecMulVec_apply]
  try ring
end ReciprocityTheory.ChartRestriction.G.SA

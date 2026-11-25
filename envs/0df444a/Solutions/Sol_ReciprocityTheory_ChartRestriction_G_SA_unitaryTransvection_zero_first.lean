-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.unitaryTransvection_zero_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:05.66635+00:00
-- url     : https://prove2.me/submissions/eeabfea0-eecc-423f-9eeb-f056f312dc02

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
theorem _root_.solution (e f : ι → K) (c : K) : eich σ J e 0 c = hm σ J e f !![1, c; 0, 1] := by
  have h0 : (σ ∘ (0 : ι → K)) = 0 := by
    funext j
    simp
  ext i j
  simp [eich, hm, h0, vecMulVec_apply]
  try ring
end ReciprocityTheory.ChartRestriction.G.SA

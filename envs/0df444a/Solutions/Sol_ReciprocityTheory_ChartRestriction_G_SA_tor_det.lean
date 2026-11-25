-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:24.959215+00:00
-- url     : https://prove2.me/submissions/bfd34cef-e3a8-4050-b2f3-2fb59aa490b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hm_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_hm

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
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (l m : K) : (tor σ J e f l m).det = l * m := by
  rw [tor_hm, hm_det hσ hJ he hff hef, Matrix.det_fin_two_of]
  ring
end ReciprocityTheory.ChartRestriction.G.SA

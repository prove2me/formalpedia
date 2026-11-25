-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.up_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:55.350806+00:00
-- url     : https://prove2.me/submissions/49c65cd3-e646-4a60-b322-c08df4c597b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_eS_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (τ : ι) : up ((eS ι r).symm (x, y)) τ = Umat y τ := by
  ext a b
  by_cases h : b < a <;> simp [up, Umat, eS_symm_apply, h]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

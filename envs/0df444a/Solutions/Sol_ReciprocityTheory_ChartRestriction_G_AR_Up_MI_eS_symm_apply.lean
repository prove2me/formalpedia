-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.eS_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:59.995802+00:00
-- url     : https://prove2.me/submissions/b1abef97-4324-4695-b297-3c8967627ed0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF

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
theorem _root_.solution (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (i : Ix ι r) :
    (eS ι r).symm (x, y) i = if h : i.2.2 < i.2.1 then x ⟨i, h⟩ else y ⟨i, h⟩ := rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

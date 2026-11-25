-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.vecL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:28.853825+00:00
-- url     : https://prove2.me/submissions/ba2243d1-e3b3-4593-b747-4908667cb111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_HasFDerivAtNmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
theorem _root_.solution (v : V (nd X)) : vecL X v = vecOf X v := rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

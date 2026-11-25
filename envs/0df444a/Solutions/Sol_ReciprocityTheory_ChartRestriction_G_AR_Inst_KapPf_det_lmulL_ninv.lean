-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_lmulL_ninv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:37:29.988246+00:00
-- url     : https://prove2.me/submissions/693ae7dc-910e-40ae-96b8-24b31dd70421

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_HasFDerivAtNmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_ninv_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_ninv_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_det_lmulL_unit


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
theorem _root_.solution (w : V (nd X)) : LinearMap.det (lmulL X (ninvF X w)) = 1 :=
  det_lmulL_unit X (ninvF X w) (fun τ a x h => ninv_lower X w τ a x h) (fun τ a => ninv_diag X w τ a)
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

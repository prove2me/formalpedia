-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.upper_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:31:03.629818+00:00
-- url     : https://prove2.me/submissions/c80cf8dc-9fad-47a3-92eb-202c0025e600

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LminorMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (B : Matrix (Fin r) (Fin r) ℂ) (hBd : B.det ≠ 0) (hB : ∀ a c : Fin r, c < a → B a c = 0) :
    ∀ a c : Fin r, c < a → B⁻¹ a c = 0 := by
  intro a c hca
  have := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hBd)
  have hBT : B.BlockTriangular id := fun i j h => hB i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular hBT) hca
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

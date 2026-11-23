-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.ninv_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:06.346652+00:00
-- url     : https://prove2.me/submissions/c49135c8-aaee-49e7-97c5-a672538b58f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_HasFDerivAtNmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_nmat_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_isUnit_nmat


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
theorem _root_.solution (w : V (nd X)) (τ : X.Ψ) (x y : Fin r) (hxy : x < y) :
    Ring.inverse (mat (nmat X w) τ) x y = 0 := by
  have : Invertible (mat (nmat X w) τ) := (isUnit_nmat X τ w).invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular (nmat_lower X w τ)
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact h hxy
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

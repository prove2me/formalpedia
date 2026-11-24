-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_rmul__da3d10a12e1f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:41.744991+00:00
-- url     : https://prove2.me/submissions/9b8b4607-686d-4334-9161-82225f347493

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instMSMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instBorelMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instSCMat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instPolishFrame
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (rmul x b) τ = mat (lact γ x) τ * mat b τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

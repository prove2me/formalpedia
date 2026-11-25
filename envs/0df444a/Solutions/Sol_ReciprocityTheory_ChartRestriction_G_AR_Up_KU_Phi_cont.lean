-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.Phi_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:04.31124+00:00
-- url     : https://prove2.me/submissions/b56dd6a2-514e-46e5-a43d-359b67c8ec6a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (Phi X x0) := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun g : Fin (Fintype.card X.Ψ) → GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ =>
      ((g (Fintype.equivFin X.Ψ τ) : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
        Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :=
    Units.continuous_val.comp (continuous_apply _)
  exact Continuous.matrix_mul continuous_const (hc.matrix_submatrix _ _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

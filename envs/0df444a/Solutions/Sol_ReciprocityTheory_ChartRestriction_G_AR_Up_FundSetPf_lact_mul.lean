-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:58.394869+00:00
-- url     : https://prove2.me/submissions/d51a5589-0361-46e0-857b-5056dca13df1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (δ δ' : GL (Fin r) E) (y : Frame Ψ r) :
    lact (δ * δ') y = lact δ (lact δ' y) := by
  funext τ
  show ((↑(δ * δ') : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) =
    (δ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf

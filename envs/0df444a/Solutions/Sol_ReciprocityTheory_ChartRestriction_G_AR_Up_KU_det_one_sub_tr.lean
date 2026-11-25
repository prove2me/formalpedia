-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.det_one_sub_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:37:30.292368+00:00
-- url     : https://prove2.me/submissions/09515b7d-9a46-44c5-80e2-a28cfebd9602

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA

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
theorem _root_.solution {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - Zᵀ * (Zᵀ)ᴴ).det = (1 - Z * Zᴴ).det := by
  rw [Matrix.det_one_sub_mul_comm]
  have : (Zᵀ)ᴴ * Zᵀ = (Z * Zᴴ)ᵀ := by
    rw [Matrix.transpose_mul]; congr 1
  rw [this, show (1 : Matrix (Fin p) (Fin p) ℂ) - (Z * Zᴴ)ᵀ = (1 - Z * Zᴴ)ᵀ by
    rw [Matrix.transpose_sub, Matrix.transpose_one], Matrix.det_transpose]
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

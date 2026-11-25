-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.posDef_Zt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:35:42.23665+00:00
-- url     : https://prove2.me/submissions/02e343da-82df-40bc-9de3-4a4bd0947bc3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_posDef_swap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff


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
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (τ : X.Ψ) : (1 - (ExF.Zt X z τ)ᵀ * ((ExF.Zt X z τ)ᵀ)ᴴ).PosDef := by
  apply posDef_swap
  have h := ((ExF.mem_OmF_iff X x0 ho z).1 hz τ).transpose
  have : ((ExF.Zt X z τ)ᵀ)ᴴ * (ExF.Zt X z τ)ᵀ = (ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ)ᵀ := by
    rw [Matrix.transpose_mul]; congr 1
  rw [this, show (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) - (ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ)ᵀ =
    (1 - ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ)ᵀ by rw [Matrix.transpose_sub, Matrix.transpose_one]]; exact h
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

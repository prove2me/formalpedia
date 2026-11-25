-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.yvec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:20.700826+00:00
-- url     : https://prove2.me/submissions/de375cb1-daa5-4106-b9c8-1d5151518cf0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_col_mul__2f207898769f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
theorem _root_.solution (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    ∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      h1 τ *ᵥ ∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b) := by
  simp only [col_mul', Matrix.mulVec_sum, Matrix.mulVec_smul]
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices

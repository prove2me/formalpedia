-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.lowBlock_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:34.87539+00:00
-- url     : https://prove2.me/submissions/8c45b284-d2f6-4265-8408-b2dba7fd7cb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices

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
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (b' b : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le b') (Fin.castLE X.p0_le b) = if b' = b then 1 else 0 := by
  have hb' := b'.isLt
  simp only [Data.lowBlock, Matrix.of_apply, Fin.castLE_inj, Fin.coe_castLE]
  rw [dif_neg (by omega)]
  simp
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices

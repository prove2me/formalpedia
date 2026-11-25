-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hatNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:26.938803+00:00
-- url     : https://prove2.me/submissions/1e0eb9cc-50b6-4a69-86d5-26f15bdb50d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_pointNorm_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.hatN la G z := by
  unfold Data.hatN
  refine Real.sSup_nonneg fun t ht => ?_
  obtain ⟨x', -, -, rfl⟩ := ht
  exact X.pointNorm_nonneg la G x'
end ReciprocityTheory.ChartRestriction.G.FD.Data

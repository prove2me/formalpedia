-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.galAct_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:25:14.488819+00:00
-- url     : https://prove2.me/submissions/b5811675-2c1e-437f-8156-2c7b70d6470e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf
theorem _root_.solution (σ : K₂ ≃ₐ[K] K₂) (x : K₂) (v : V) :
    galAct σ (x ⊗ₜ[K] v) = σ x ⊗ₜ[K] v := by
  simp [galAct]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf

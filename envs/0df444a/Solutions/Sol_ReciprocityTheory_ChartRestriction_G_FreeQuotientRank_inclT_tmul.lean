-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.inclT_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:40.907252+00:00
-- url     : https://prove2.me/submissions/8f3a3315-2e30-460b-95df-872fc66c5871

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_inclT_tmul__4dfde58e6361

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
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) • ((1 : Ω) ⊗ₜ[K] v) := by
  rw [inclT_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

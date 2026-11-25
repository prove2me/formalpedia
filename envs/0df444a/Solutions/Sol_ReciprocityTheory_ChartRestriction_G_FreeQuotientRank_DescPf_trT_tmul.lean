-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf.trT_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:06.408123+00:00
-- url     : https://prove2.me/submissions/608dee8f-0bc9-4aa6-aa02-64be2bf09a1b

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
theorem _root_.solution [FiniteDimensional K K₂] (x : K₂) (v : V) :
    trT (x ⊗ₜ[K] v) = Algebra.trace K K₂ x • v := by
  simp [trT]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.DescPf

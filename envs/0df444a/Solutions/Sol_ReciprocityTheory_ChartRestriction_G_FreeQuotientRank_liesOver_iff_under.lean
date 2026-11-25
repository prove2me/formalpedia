-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.liesOver_iff_under
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:13.115591+00:00
-- url     : https://prove2.me/submissions/afe77f1a-7c95-43a6-b9d6-23f7a46401ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) :
    LiesOver w la ↔ under (K := K) w = la := by
  unfold LiesOver
  constructor
  · intro h
    exact HeightOneSpectrum.ext h
  · intro h
    subst h
    rfl
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

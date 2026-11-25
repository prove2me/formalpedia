-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finite_ordAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:41.973294+00:00
-- url     : https://prove2.me/submissions/c2624585-446d-4cd1-abd3-6e4a6229e4c4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finite_mulSupport_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_support_ordAt_sub

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
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v).Finite :=
  (finite_mulSupport_emb hx).subset (support_ordAt_sub hx)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

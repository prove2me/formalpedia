-- Prove2me | solution 1 for UnipMove.sCmp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:35.001296+00:00
-- url     : https://prove2.me/submissions/5136cf5a-c8de-4ea9-b9b6-8f2231636414

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoNormRelationTamePrime
import Theorems.Thm_UnipMove_sMajFlag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_xZ_mem_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution (hm : SMajXZ E) : SCmp E := by
  intro r X x0 hx0 ho ρ' h1 h2 Z1 hZ1 z hz hsf τ v
  have hdom : X.xZ x0 Z1 ∈ X.dom := OrthonormalChartBounds.xZ_mem_dom X hx0 ho (by linarith)
  rw [sMajFlag r X z _ hz hdom hsf]
  exact hm r X x0 hx0 ho ρ' h1 h2 Z1 hZ1 τ v
end UnipMove

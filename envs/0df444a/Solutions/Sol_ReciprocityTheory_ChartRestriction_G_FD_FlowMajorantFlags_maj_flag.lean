-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:29:08.533095+00:00
-- url     : https://prove2.me/submissions/01c2495b-ab27-4442-877e-a841ce5a64d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_Hf_flag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
theorem _root_.solution {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj z' τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hz' τ, ← X.Hf_self hz τ, Hf_flag X hz hz' hf]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags

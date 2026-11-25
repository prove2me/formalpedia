-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:26.625091+00:00
-- url     : https://prove2.me/submissions/4e38a43d-e664-4be9-a703-64d20491ea78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_Hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_Hf_smul_right
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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((k : ℂ) • v) = k ^ 2 * X.maj x τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hx τ, Hf_smul_left, Hf_smul_right, X.Hf_self hx τ, Complex.conj_ofReal]
  push_cast; ring
end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags

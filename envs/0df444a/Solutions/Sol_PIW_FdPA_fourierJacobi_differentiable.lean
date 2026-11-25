-- Prove2me | solution 1 for PIW.FdPA.fourierJacobi_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:26.19625+00:00
-- url     : https://prove2.me/submissions/d0718193-cd58-4d4a-b975-cfa0a5a18d04

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_FourierJacobiDifferentiable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_CuspCoefficientFlow_fj_diffOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : FjDiff E := by
  intro r X la P ξ ν hP hξ
  exact CuspCoefficientFlow.fj_diffOn (X := X) la P hP hξ ν
end PIW.FdPA

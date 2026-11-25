-- Prove2me | solution 1 for PIW.FdPA.chart_zero_eq_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:19:41.85831+00:00
-- url     : https://prove2.me/submissions/50254bae-23d7-483f-afc8-25e1bf7ce60a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : XZZero E := by
  intro r X x
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  simp only [Data.xZ, h1, Matrix.mul_one]
  rfl
end PIW.FdPA

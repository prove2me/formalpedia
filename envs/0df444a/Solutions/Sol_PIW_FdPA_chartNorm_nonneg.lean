-- Prove2me | solution 1 for PIW.FdPA.chartNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:45.907628+00:00
-- url     : https://prove2.me/submissions/6a4daaf0-d673-4545-9e3d-5990d8637fe4

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : ZnNonneg E := by
  intro r X Z
  unfold Data.zN
  refine Real.iSup_nonneg (fun τ => ?_)
  unfold Data.opN
  refine Real.sSup_nonneg (fun t ht => ?_)
  obtain ⟨v, _, rfl⟩ := ht
  positivity
end PIW.FdPA

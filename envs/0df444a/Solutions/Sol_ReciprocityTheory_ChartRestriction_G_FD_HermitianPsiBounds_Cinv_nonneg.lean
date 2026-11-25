-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.Cinv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:09.251809+00:00
-- url     : https://prove2.me/submissions/9fa8b659-7c3e-4d75-90ce-26fd66d0d9c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPsiBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
theorem _root_.solution : 0 ≤ Cinv X := by
  unfold Cinv
  exact Finset.sum_nonneg fun τ _ => by unfold Data.c; positivity
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds

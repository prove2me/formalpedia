-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.inv_c_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:07.004002+00:00
-- url     : https://prove2.me/submissions/cadb5dd4-a7ed-48cf-8514-3680ae8a43d3

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
theorem _root_.solution (τ : X.Ψ) : 1 / X.c τ ≤ Cinv X := by
  unfold Cinv
  exact Finset.single_le_sum (f := fun τ => 1 / X.c τ)
    (fun τ' _ => by unfold Data.c; positivity) (Finset.mem_univ τ)
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds

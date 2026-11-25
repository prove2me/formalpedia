-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_cont_gram__06583ee5c83d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:09.068571+00:00
-- url     : https://prove2.me/submissions/9badaee3-71f8-4098-8430-ac5c97f2ae1e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
theorem _root_.solution (τ : X.Ψ) : Continuous fun w : Frame X.Ψ r => gram τ.1 X.Gm (mat w τ) := by
  apply continuous_matrix
  intro a b
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds

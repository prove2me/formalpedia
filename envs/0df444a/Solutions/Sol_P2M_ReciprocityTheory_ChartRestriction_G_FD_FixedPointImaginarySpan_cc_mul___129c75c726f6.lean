-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_cc_mul___129c75c726f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:55.411968+00:00
-- url     : https://prove2.me/submissions/5c3eab8e-d865-4f2d-b802-d765765d4943

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
theorem _root_.solution (x y : E) : cc (x * y) = cc x * cc y := map_mul (IsCMField.complexConj E) x y
end ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan

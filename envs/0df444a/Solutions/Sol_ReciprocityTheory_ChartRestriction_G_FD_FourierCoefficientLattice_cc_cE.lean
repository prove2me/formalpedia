-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.cc_cE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:52.574018+00:00
-- url     : https://prove2.me/submissions/1f80df2b-208e-4a47-8159-2eda63bd767a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
theorem _root_.solution : cc (cE (E := E) g) = cE g := by
  simp only [cc, cE, map_div₀, map_natCast, map_ofNat]
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice

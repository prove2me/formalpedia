-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.embV_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:59.986729+00:00
-- url     : https://prove2.me/submissions/2272eb13-9bc1-43fb-8eb8-c17e86cff6fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
theorem _root_.solution (n : ℤ) (w : Fin r → E) : X.embV (n • w) = (n : ℝ) • X.embV w := by
  funext τ a
  simp only [Data.embV, Data.emb, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast,
    Complex.real_smul, Complex.ofReal_intCast]
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms

-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_cc__L_a00542ceadc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:00.252745+00:00
-- url     : https://prove2.me/submissions/63e9f0c9-b759-408d-b54f-d0afd55338ef

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
theorem _root_.solution (C : ChartAt Xo c y) (m : ℕ) (p : Fin 2 × Fin C.d) : MvPolynomial.constantCoeff (σL C m p) = 0 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> simp [σL, psIn, MvPolynomial.constantCoeff_rename, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', C.B.A.const]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

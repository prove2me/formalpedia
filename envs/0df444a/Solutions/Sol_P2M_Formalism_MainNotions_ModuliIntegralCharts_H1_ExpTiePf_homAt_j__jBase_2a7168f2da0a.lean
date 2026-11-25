-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_homAt_j__jBase_2a7168f2da0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:16.243602+00:00
-- url     : https://prove2.me/submissions/3c516f6e-6f8f-4efd-976a-87d67c637fca

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    Formalism.L2.Pj.homAt y.x (jφ φ m) ≫ jBase y C.d m 1 = jBase y (dL Dw) m 1 := by
  apply Over.OverMorphism.ext
  exact spMap_comp_alg (jφ φ m)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTiePf

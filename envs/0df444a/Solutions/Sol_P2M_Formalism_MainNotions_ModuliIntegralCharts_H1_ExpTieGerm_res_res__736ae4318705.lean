-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_res_res__736ae4318705
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:52.280498+00:00
-- url     : https://prove2.me/submissions/48b82982-0d00-4def-9c05-4edbef1cb96d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
theorem _root_.solution {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x :=
  ReciprocityTheory.ChartRestriction.G.DVR.res_res' h1 h2 x
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm

-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_gam_to__114d125ac7f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:17.440802+00:00
-- url     : https://prove2.me/submissions/93c222ef-34e6-4acf-ae66-f7048148d049

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeBeta
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqD

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution (A : Type) [CommRing A] (a : A) : gam A (toΓ A a) = a := by
  simp [gam, toΓ]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR

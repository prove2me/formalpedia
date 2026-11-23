-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_to__injective_2d1b9ff55e5a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:21.10786+00:00
-- url     : https://prove2.me/submissions/27ebe4d8-1c24-4e0a-8c20-63ba3147b25b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf

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
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
theorem _root_.solution (S : Type) [CommRing S] : Function.Injective (toΓ S) := by
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

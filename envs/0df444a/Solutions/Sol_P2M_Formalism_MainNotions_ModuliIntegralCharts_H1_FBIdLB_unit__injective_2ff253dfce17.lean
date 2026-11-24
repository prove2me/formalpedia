-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__injective_2ff253dfce17
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:59.235678+00:00
-- url     : https://prove2.me/submissions/844a9e02-8bf7-401e-bab5-04b7185366eb

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
theorem _root_.solution {A : Type} [CommRing A] : Function.Injective (unitΓ (A := A)) := by
  intro u u' h
  ext
  have h1 := congrArg Units.val h
  simp only [unitΓ, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, toΓ] at h1
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom h1
  simpa using h2
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB

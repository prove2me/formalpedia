-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_single__0fef72d07d07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:47.138777+00:00
-- url     : https://prove2.me/submissions/5b139e45-dbb7-414a-97fb-4b061eed85c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
variable {M : LB A.left}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {α β : Type} (f : α → β) (a : α) (n : ℤ) :
    Finsupp.mapDomain f (Finsupp.single a n) = Finsupp.single (f a) n := by
  exact Finsupp.mapDomain_single
end ReciprocityTheory.ChartRestriction.G.DVR

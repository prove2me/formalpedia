-- Prove2me | solution 1 for P2M_GlobalTheory_CommutatorPairing_overLE___bed2ac08eb35
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:15.135794+00:00
-- url     : https://prove2.me/submissions/0fa3e7f0-71c7-479e-80d2-4a7794c872af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution {T : Over S} {V W : T.left.Opens} (h : V ≤ W) : overLE h ≫ overResι W = overResι V :=
  Over.OverMorphism.ext (T.left.homOfLE_ι h)
end GlobalTheory.CommutatorPairing

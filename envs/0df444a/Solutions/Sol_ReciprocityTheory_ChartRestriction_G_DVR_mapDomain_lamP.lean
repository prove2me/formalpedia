-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.mapDomain_lamP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:26:20.382129+00:00
-- url     : https://prove2.me/submissions/c0512a6e-998e-4791-b1fe-2507ec52e702

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
theorem _root_.solution (h : T' ⟶ T) (u v : T ⟶ A) :
    Finsupp.mapDomain (fun x => h ≫ x) (lamP u v) = lamP (h ≫ u) (h ≫ v) := by
  unfold lamP
  have hs : ∀ (P Q : (T ⟶ A) →₀ ℤ), Finsupp.mapDomain (fun x => h ≫ x) (P - Q) =
      Finsupp.mapDomain (fun x => h ≫ x) P - Finsupp.mapDomain (fun x => h ≫ x) Q :=
    fun P Q => map_sub (Finsupp.mapDomain.addMonoidHom _) P Q
  rw [Finsupp.mapDomain_add, hs, hs, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, MonObj.comp_mul,
    MonObj.comp_one]
end ReciprocityTheory.ChartRestriction.G.DVR

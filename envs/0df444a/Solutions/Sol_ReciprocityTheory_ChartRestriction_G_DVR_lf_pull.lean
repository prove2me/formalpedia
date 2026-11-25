-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.lf_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:33.550782+00:00
-- url     : https://prove2.me/submissions/976be538-eb3a-48d4-bad1-4c41545241c9

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
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (h : T' ⟶ T) (F : (T ⟶ A) →₀ ℤ) :
    Finsupp.mapDomain (fun ψ => h.left ≫ ψ) (lf F) = lf (Finsupp.mapDomain (fun x => h ≫ x) F) := by
  unfold lf
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR

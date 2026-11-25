-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.le_comp_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:55.299495+00:00
-- url     : https://prove2.me/submissions/fe162d93-b473-4153-9722-f4d19927c64c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z Y Y' X : Scheme.{0}} {f : Z ⟶ Y} {g : Y ⟶ X} {f' : Z ⟶ Y'} {g' : Y' ⟶ X}
    (h : f ≫ g = f' ≫ g') {U : X.Opens} {O : Z.Opens} (hO : O ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    O ≤ (f' ≫ g') ⁻¹ᵁ U := by
  rw [← h]
  exact hO
end ReciprocityTheory.ChartRestriction.G.DVR

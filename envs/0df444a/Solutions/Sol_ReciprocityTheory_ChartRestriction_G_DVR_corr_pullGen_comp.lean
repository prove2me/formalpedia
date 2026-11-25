-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:04:07.777742+00:00
-- url     : https://prove2.me/submissions/1b4a28ee-3041-467c-b92b-15bc334cd629

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_pull_comp

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {W : Scheme.{0}} (t : LB.Gen (LB.LinComb L φ ε)) (g : Z ⟶ Y) (g' : W ⟶ Z) :
    LB.Gen.Corr L _ ε _ ε (LB.pullGen L _ ε (LB.pullGen L φ ε t g) g') (LB.pullGen L φ ε t (g' ≫ g)) := by
  intro j j' _ _ hk
  obtain rfl : j = j' := funext fun k => hk k k (Category.assoc _ _ _).symm
  exact shape_pull_comp g g' _ _ _ _ _ _
end ReciprocityTheory.ChartRestriction.G.DVR

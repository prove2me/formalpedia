-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen_invGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:07.815378+00:00
-- url     : https://prove2.me/submissions/ba0a8c3e-6bca-4462-a358-6cbb77ac7048

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_pull_inv

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
theorem _root_.solution (t : LB.Gen (LB.LinComb L φ ε)) (g : Z ⟶ Y) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (LB.invGen L φ ε t) g) (LB.invGen L _ _ (LB.pullGen L φ ε t g)) := by
  intro j j' _ _ hk
  obtain rfl : j = j' := funext fun k => hk k k rfl
  exact shape_pull_inv g _ _ _ _ _
end ReciprocityTheory.ChartRestriction.G.DVR

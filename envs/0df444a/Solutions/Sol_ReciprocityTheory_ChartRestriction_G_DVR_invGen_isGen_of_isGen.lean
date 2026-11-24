-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen_of_isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:19.768138+00:00
-- url     : https://prove2.me/submissions/e0eea31e-8dd5-483b-af95-d7631fcf7b5c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr

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
theorem _root_.solution (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : (LB.invGen L φ ε t).IsGen := by
  intro (i : K → L.ι) (j : K → L.ι)
  have e := ht i j
  have hinv : (LB.LinComb L φ (fun k => -ε k)).g i j = ((LB.LinComb L φ ε).g i j)⁻¹ := by
    simp only [LB.LinComb, zpow_neg, Finset.prod_inv_distrib]
    rfl
  exact (map_inv _ _).trans ((congrArg (·⁻¹) e).trans ((mul_inv _ _).trans
    (congrArg₂ (· * ·) hinv.symm (map_inv _ _).symm)))
end ReciprocityTheory.ChartRestriction.G.DVR

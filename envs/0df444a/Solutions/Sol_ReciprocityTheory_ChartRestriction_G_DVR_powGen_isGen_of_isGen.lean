-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen_of_isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:45.736274+00:00
-- url     : https://prove2.me/submissions/1960654c-538c-4101-b907-5239b224314a

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
theorem _root_.solution (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.Out.GeneratorPullback.powGen L φ ε t n).IsGen := by
  intro (i : K → L.ι) (j : K → L.ι)
  have e := ht i j
  have hg : (LB.LinComb L φ (fun k => (n : ℤ) * ε k)).g i j = ((LB.LinComb L φ ε).g i j) ^ n := by
    simp only [LB.LinComb, mul_comm (n : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]
    rfl
  exact (map_pow _ _ _).trans ((congrArg (· ^ n) e).trans ((mul_pow _ _ _).trans
    (congrArg₂ (· * ·) hg.symm (map_pow _ _ _).symm)))
end ReciprocityTheory.ChartRestriction.G.DVR

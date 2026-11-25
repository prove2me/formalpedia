-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:11.927908+00:00
-- url     : https://prove2.me/submissions/ff7a36a1-cd08-434e-95d5-501fc96e75c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_product_generator_isGenerator

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := fun i j => product_generator_isGenerator L φ ε φ' ε' t t' ht ht' i j
end ReciprocityTheory.ChartRestriction.G.DVR

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen_of_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:16.521103+00:00
-- url     : https://prove2.me/submissions/bb25dd10-7292-489f-a375-aedaf45c6e16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_units_compat_generic

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
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (h : Z ⟶ Y) : (LB.pullGen L φ ε t h).IsGen := by
  intro i j
  exact pullU_units_compat_generic h (wchart_comp_le φ h i) (wchart_comp_le φ h j) (t.s i) (t.s j) _ (ht i j) _
    (linComb_g_comp φ ε h i j)
end ReciprocityTheory.ChartRestriction.G.DVR

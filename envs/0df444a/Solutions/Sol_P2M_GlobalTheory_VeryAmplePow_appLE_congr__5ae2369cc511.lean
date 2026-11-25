-- Prove2me | solution 1 for P2M_GlobalTheory_VeryAmplePow_appLE_congr__5ae2369cc511
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:33:51.934106+00:00
-- url     : https://prove2.me/submissions/380dc591-cea7-452c-941a-25a26b3d16f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (e : g = g') {U : Y.Opens} {V : Z.Opens} (h : V ≤ g ⁻¹ᵁ U) :
    g.appLE U V h = g'.appLE U V (e ▸ h) := by subst e; rfl
end GlobalTheory.VeryAmplePow

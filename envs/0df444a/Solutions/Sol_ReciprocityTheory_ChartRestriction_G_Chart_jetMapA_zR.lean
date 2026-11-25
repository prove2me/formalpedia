-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jetMapA_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:56:51.569865+00:00
-- url     : https://prove2.me/submissions/f53fc0d5-25c3-4cef-be4b-f85300777970

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] (eps : B →ₐ[R] R) {n : ℕ}
variable {R' : Type} [CommRing R'] [Algebra R R']
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (m : ℕ) (j : Fin n) : jetMapA (R := R) (R' := R') n m (zR m j) = zR m j := by
  unfold jetMapA
  rw [jetLift_zR]
end ReciprocityTheory.ChartRestriction.G.Chart

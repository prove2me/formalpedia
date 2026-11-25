-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.smul_mem_pts_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:08.681689+00:00
-- url     : https://prove2.me/submissions/e6bbe483-ab13-4995-9a1f-00bbbd9b7cc2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupLeL2NormSections
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_smul_of_isHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coordIdeal_isHomogIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩
  have hH := coordIdeal_isHomogIdeal ℤ x
  rw [← sum_homogeneousComponent f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous ((homogeneousComponent_isHomogeneous d f).map _),
    hz.2 _ (hH f hf d), mul_zero]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

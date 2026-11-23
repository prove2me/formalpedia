-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:38.111802+00:00
-- url     : https://prove2.me/submissions/aeec1bff-883f-4eef-adaa-3f9164ccc122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

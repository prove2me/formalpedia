-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.det_sub_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:43.603356+00:00
-- url     : https://prove2.me/submissions/884ba22e-b17b-4c0c-a687-2aa8a08eed11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {i : ℕ} (h : i ≤ n) {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) :
    (N.submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ j : Fin i, N (Fin.castLE h j) (Fin.castLE h j) := by
  have ht : (N.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := fun a c hca =>
    hN (show Fin.castLE h c < Fin.castLE h a from hca)
  rw [Matrix.det_of_isUpperTriangular ht]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

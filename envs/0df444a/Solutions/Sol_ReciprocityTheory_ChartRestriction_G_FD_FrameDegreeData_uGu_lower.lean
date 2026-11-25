-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uGu_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:24:51.90613+00:00
-- url     : https://prove2.me/submissions/908d9980-91f8-4a89-92d9-f69a75951968

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_upper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uT_G_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_upper_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution (G : Matrix (Fin n) (Fin n) ℂ) (hdet : ∀ c : Fin n, (blk G c).det ≠ 0) {a c : Fin n}
    (hac : a < c) : ((uMat G)ᵀ * G * (uMat G).map (starRingEnd ℂ)) c a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge a k with h | h
  · rw [Matrix.map_apply, upper_lt (uMat_upper G) h, map_zero, mul_zero]
  · rw [uT_G_zero G c (hdet c) k (lt_of_le_of_lt h hac), zero_mul]
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

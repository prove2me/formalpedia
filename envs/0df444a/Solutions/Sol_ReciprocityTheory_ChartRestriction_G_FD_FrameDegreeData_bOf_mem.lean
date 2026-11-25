-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:38:45.610886+00:00
-- url     : https://prove2.me/submissions/ca62a1c6-fbdc-4ced-9ed5-723102e28f30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sOf_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uMat_upper
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) : bOf X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)).det ≠ 0
    unfold uOf
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_of_upperTriangular (uMat_upper _)]
    simp only [uMat_diag, Finset.prod_const_one, one_mul]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => sOf_ne X hx τ k
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)) a c = 0
    unfold uOf
    rw [Matrix.mul_diagonal, upper_lt (uMat_upper _) hca, zero_mul]
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

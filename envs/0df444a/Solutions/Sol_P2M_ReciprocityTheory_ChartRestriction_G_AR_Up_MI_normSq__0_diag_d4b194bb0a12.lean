-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_normSq__0_diag_d4b194bb0a12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:30:28.933797+00:00
-- url     : https://prove2.me/submissions/fa8971b9-a530-422c-b301-3c6c8b09e96f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_upper_mul_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_bOf_diag
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_upper_9db1d5f297f4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_bOf_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_abs_re_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_upper_of_bor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    Complex.normSq (β0 X y τ k k) = |(dOf X y τ k).re| := by
  have hinv : β0 X y τ * mat (bOf X y) τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  have h1 := congrFun (congrFun hinv k) k
  rw [upper_mul_diag (β0_upper X hy τ) (upper_of_bor X (bOf_mem X hy) τ), bOf_diag, Matrix.one_apply_eq] at h1
  have hpos := abs_re_pos X hy τ k
  have hs : Complex.normSq (sOf X y τ k) = |(dOf X y τ k).re|⁻¹ := by
    rw [sOf, Complex.normSq_ofReal, ← pow_two, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_mul, hs, map_one] at h2
  field_simp at h2
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

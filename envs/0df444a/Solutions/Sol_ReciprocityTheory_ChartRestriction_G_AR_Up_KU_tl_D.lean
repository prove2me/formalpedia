-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.tl_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:14.511686+00:00
-- url     : https://prove2.me/submissions/fccb2251-cb09-42d5-b308-59923c055066

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_eT_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_eT_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) :
    tl X (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) = -Jf (r - X.p0) X.p0 := by
  ext a b
  rcases a with j | i <;> rcases b with j' | i'
  · simp only [tl, Matrix.submatrix_apply, eT_inl, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.diagonal_apply, Matrix.one_apply, ExF.qI, Fin.ext_iff, Nat.add_left_cancel_iff]
    split_ifs <;> simp [sgn]
  · simp only [tl, Matrix.submatrix_apply, eT_inl, eT_inr, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, ExF.qI, Fin.ext_iff, Fin.coe_castLE, Matrix.zero_apply, neg_zero]
    rw [if_neg]; have := i'.isLt; omega
  · simp only [tl, Matrix.submatrix_apply, eT_inl, eT_inr, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, ExF.qI, Fin.ext_iff, Fin.coe_castLE, Matrix.zero_apply, neg_zero]
    rw [if_neg]; have := i.isLt; omega
  · simp only [tl, Matrix.submatrix_apply, eT_inr, Jf, Matrix.neg_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply, Fin.ext_iff, Fin.coe_castLE, neg_neg]
    split_ifs with h <;> simp [sgn, i.isLt]
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

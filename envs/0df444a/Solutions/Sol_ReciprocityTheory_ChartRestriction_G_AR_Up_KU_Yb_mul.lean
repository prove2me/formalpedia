-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.Yb_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:06.957327+00:00
-- url     : https://prove2.me/submissions/769018ae-09ff-44ce-a037-3eac0d884d38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_4f0f1441775d
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_2640c3b66a1c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution {p q : ℕ} (g M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hM : M.toBlocks₂₂.det ≠ 0) :
    Yb (g * M) = mob g (Yb M) := by
  have hu : IsUnit M.toBlocks₂₂.det := isUnit_iff_ne_zero.mpr hM
  have h12 : M.toBlocks₁₂ = Yb M * M.toBlocks₂₂ := by
    rw [Yb, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have e1 : (g * M).toBlocks₁₂ = (g.toBlocks₁₁ * Yb M + g.toBlocks₁₂) * M.toBlocks₂₂ := by
    rw [toBlocks₁₂_mul, h12, Matrix.add_mul, Matrix.mul_assoc]
  have e2 : (g * M).toBlocks₂₂ = (g.toBlocks₂₁ * Yb M + g.toBlocks₂₂) * M.toBlocks₂₂ := by
    rw [toBlocks₂₂_mul, h12, Matrix.add_mul, Matrix.mul_assoc]
  rw [Yb, e1, e2, Matrix.mul_inv_rev, mob, Matrix.mul_assoc, ← Matrix.mul_assoc M.toBlocks₂₂,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

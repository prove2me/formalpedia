-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.gramPos_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:05.359148+00:00
-- url     : https://prove2.me/submissions/2463c211-fd16-498e-a892-6a1a734261f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mat_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_sum_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_sum_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    X.gramPos (cpt X x0 z) τ =
      (n1 X z τ)ᵀ * (n1 X z τ).map (starRingEnd ℂ) - (Wm X z τ)ᵀ * (Wm X z τ).map (starRingEnd ℂ) := by
  have hg : gram τ.1 X.Gm (mat (cpt X x0 z) τ) = (nM X z τ)ᵀ *
      Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
        (nM X z τ).map (starRingEnd ℂ) := by
    rw [mat_cpt, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, ho τ]
  ext c d
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Data.gramPos, hg, Matrix.submatrix_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, n1, Wm,
    Matrix.submatrix_apply]
  rw [sum_split X, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    have he : ((Fin.castLE X.p0_le e : Fin r) : ℕ) < X.p0 := by simp
    simp [sgn, he]
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : ¬ ((qI X m : Fin r) : ℕ) < X.p0 := by simp [qI]
    simp [sgn, hm]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

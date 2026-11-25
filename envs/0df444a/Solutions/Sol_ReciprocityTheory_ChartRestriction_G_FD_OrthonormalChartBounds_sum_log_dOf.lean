-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.sum_log_dOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:09.716003+00:00
-- url     : https://prove2.me/submissions/b40d939a-004c-47d4-8f8a-44d38dacffa0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PivotNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_norm_dOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dmin_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sgn_dOf_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_det_lowBlock
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_gram_xZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_xZ_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_lminor_last


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) : ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ = 0 := by
  have hy := xZ_mem_dom X hx ho hZ
  have hpos : ∀ k, ‖dOf X (X.xZ x Z) τ k‖ ≠ 0 := fun k => by
    rw [norm_dOf X hy τ k]
    apply (abs_pos.2 _).ne'
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [← Real.log_prod (fun k _ => hpos k), ← norm_prod]
  have hp : ∏ k : Fin r, dOf X (X.xZ x Z) τ k = dmin X.Gm (X.xZ x Z) τ (Fin.last r) := by
    rw [dmin_prod X hy τ (Fin.last r)]
    rfl
  rw [hp]
  unfold dmin
  rw [gram_xZ X ho Z τ, lminor_last]
  unfold Gp
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_lowBlock, Matrix.det_diagonal, one_mul]
  rw [show ((X.lowBlock Z τ).map (starRingEnd ℂ)).det = (starRingEnd ℂ) (X.lowBlock Z τ).det from
    (RingHom.map_det _ _).symm, det_lowBlock, map_one, mul_one, norm_prod]
  rw [Finset.prod_eq_one fun k _ => ?_, Real.log_one]
  unfold sgn
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

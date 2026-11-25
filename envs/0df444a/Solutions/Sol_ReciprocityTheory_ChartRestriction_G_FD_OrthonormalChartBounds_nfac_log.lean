-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.nfac_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:11:10.245548+00:00
-- url     : https://prove2.me/submissions/c3d3928a-2bd0-4cb8-85a0-2ba7422e2952

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PivotNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_norm_dOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_ratio_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sgn_dOf_pos


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
theorem _root_.solution {y : Frame X.Ψ r} (hy : y ∈ X.dom) (la : Wt X.Ψ r) :
    Real.log (X.nfac la y) = ∑ τ, ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X y τ k‖ := by
  unfold Data.nfac
  have hpos : ∀ τ k, 0 < ‖dOf X y τ k‖ := fun τ k => by
    rw [norm_dOf X hy τ k]
    apply abs_pos.2
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (by
      rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun k _ => (Real.rpow_pos_of_pos (by rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ratio_eq X hy τ k, Real.log_rpow (hpos τ k)]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

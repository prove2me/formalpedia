-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_re_trace_eq_c0fe8cc86955
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:22.895747+00:00
-- url     : https://prove2.me/submissions/8d871aa3-0b98-465d-abb3-20e0ce375fdf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Matrix Metric Real
open scoped MatrixOrder ComplexOrder
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution (W : Matrix ι κ ℂ) (Y : Matrix ι ι ℝ) :
    RCLike.re (Wᴴ * cx Y * W).trace =
      ∑ j, ∑ k, (∑ a, (star (W j a) * W k a).re) * Y j k := by
  calc RCLike.re (Wᴴ * cx Y * W).trace
      = ∑ a, ∑ k, ∑ j, (star (W j a) * W k a).re * Y j k := by
        simp only [trace, diag, mul_apply, conjTranspose_apply, map_apply, RCLike.re_to_complex,
          Complex.re_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
    _ = ∑ j, ∑ k, ∑ a, (star (W j a) * W k a).re * Y j k := by
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.sum_mul]
end GroundTheory.Heights₂.Heights.MCPsh

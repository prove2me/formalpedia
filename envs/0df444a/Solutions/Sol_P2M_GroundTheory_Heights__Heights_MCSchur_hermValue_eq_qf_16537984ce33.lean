-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:14.513802+00:00
-- url     : https://prove2.me/submissions/24a124ed-906f-460f-892a-fb45d8f2ed20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCSchur
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCSchur
theorem _root_.solution {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    hermValue A w = qf A (fun k => (w k).re) + qf A (fun k => (w k).im) := by
  simp only [hermValue, hermPair, qf, dotProduct, mulVec, Matrix.map_apply, Complex.re_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring
end GroundTheory.Heights₂.Heights.MCSchur

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_hermPair_symm_5f1a589f163b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:14.004078+00:00
-- url     : https://prove2.me/submissions/65f0366c-516b-4756-a00b-62ba20b19bde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodGramPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.PeriodGramPosDef
namespace GroundTheory.Heights₂.Heights.PeriodGramPosDef
theorem _root_.solution {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (v w : ι → ℂ) :
    hermPair A v w = hermPair A w v := by
  simp only [hermPair, dotProduct, mulVec, Matrix.map_apply, Complex.re_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hkl : A l k = A k l := by rw [← transpose_apply A k l, hA]
  rw [hkl]
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring
end GroundTheory.Heights₂.Heights.PeriodGramPosDef

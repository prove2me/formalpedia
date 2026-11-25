-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodLatticeCovolume_hermPair_comb_de07ed4153bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:28.0978+00:00
-- url     : https://prove2.me/submissions/c9c1d1dc-3ff0-4a9c-8ec9-4eae9f2d5be4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodLatticeCovolume

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
open GroundTheory.Heights₂.Heights.PeriodLatticeCovolume
namespace GroundTheory.Heights₂.Heights.PeriodLatticeCovolume
theorem _root_.solution {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix ι ι ℝ) (b : Fin m → ι → ℂ)
    (x y : Fin m → ℝ) :
    hermPair A (∑ a, (x a : ℂ) • b a) (∑ c, (y c : ℂ) • b c) =
      ∑ a, ∑ c, x a * y c * hermPair A (b a) (b c) := by
  unfold hermPair
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_sum,
    mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.re_sum, Complex.re_ofReal_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring
end GroundTheory.Heights₂.Heights.PeriodLatticeCovolume

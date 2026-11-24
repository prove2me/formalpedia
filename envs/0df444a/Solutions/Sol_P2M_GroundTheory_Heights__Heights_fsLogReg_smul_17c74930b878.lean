-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fsLogReg_smul_17c74930b878
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:39.425527+00:00
-- url     : https://prove2.me/submissions/763782c4-e75a-490c-8f3c-375fd0f36f3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (t : ℂ) (x : Fin n → ℂ)
    (ht : t ≠ 0) : fsLogReg h u ε (t • x) = fsLogReg h u ε x := by
  have hs : ∑ j, u j * (t • x) j = t * ∑ j, u j * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  unfold fsLogReg
  rw [hs, h.dualNorm_smul, norm_mul, mul_pow, mul_pow, mul_left_comm ε, ← mul_add,
    mul_div_mul_left _ _ ht2]
end GroundTheory.Heights₂.Heights

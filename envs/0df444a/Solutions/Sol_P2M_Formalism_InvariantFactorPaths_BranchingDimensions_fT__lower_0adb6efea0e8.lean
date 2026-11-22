-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__lower_0adb6efea0e8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:18.356009+00:00
-- url     : https://prove2.me/submissions/09d2526b-eff6-43a9-b3b2-8ed2c13798cf

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : (k' : ℝ) / (y + k') ≤ fT' k' y := by
  unfold fT'
  have : (k' : ℝ) / (y + k') = ∑ _j ∈ Icc 1 k', 1 / (y + (k' : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp [div_eq_mul_inv]
  rw [this]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hj2 : (j : ℝ) ≤ k' := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  apply one_div_le_one_div_of_le (by positivity) (by linarith)
end Formalism.InvariantFactorPaths.BranchingDimensions

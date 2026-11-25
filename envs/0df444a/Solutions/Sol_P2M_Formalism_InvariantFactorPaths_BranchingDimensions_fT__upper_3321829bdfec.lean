-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_BranchingDimensions_fT__upper_3321829bdfec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:17.50785+00:00
-- url     : https://prove2.me/submissions/3be65b6a-cce9-4081-a06f-4f4c2fcc1866

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
theorem _root_.solution (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : fT' k' y ≤ (k' : ℝ) / (y + 1) := by
  unfold fT'
  have : (k' : ℝ) / (y + 1) = ∑ _j ∈ Icc 1 k', 1 / (y + (1 : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp [div_eq_mul_inv]
  rw [this]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  apply one_div_le_one_div_of_le (by positivity) (by linarith)
end Formalism.InvariantFactorPaths.BranchingDimensions

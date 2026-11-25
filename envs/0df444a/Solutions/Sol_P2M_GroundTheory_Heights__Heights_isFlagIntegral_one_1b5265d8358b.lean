-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isFlagIntegral_one_1b5265d8358b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:36.300316+00:00
-- url     : https://prove2.me/submissions/b76d5b90-cb2e-4b93-8ac2-2c65bd8f4d8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest

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
open MvPolynomial Matrix Real
noncomputable section
variable (f j k : ℕ)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : IsFlagIntegral 1 1 1 flagIntegralOne where
  kills := by
    intro m τ G h1 h2 _
    have hD : flagDim 1 1 1 = 1 := by decide
    have hm : m = 1 := by omega
    subst hm
    fin_cases τ
    simp [flagIntegralOne, rootPsum, Fintype.sum_sum_type, add_mul, coeff_X_mul']
  ne_zero := by
    refine ⟨X (0, Sum.inl 0), ?_, ?_⟩
    · have hD : flagDim 1 1 1 = 1 := by decide
      rw [hD]; exact isHomogeneous_X _ _
    · simp [flagIntegralOne, coeff_X, Finsupp.single_eq_single_iff]
end GroundTheory.Heights₂.Heights

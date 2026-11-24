-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_mul_I_ff45644aceb5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:05.101167+00:00
-- url     : https://prove2.me/submissions/ac361cbb-9108-4fa8-b65a-a85e59e32920

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_mul_6ed98b2144e6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (ν : ℕ) (k : ℤ) (w : ℂ) :
    thetaThree ν (w + k * I) =
      cexp (-(3 * π * I * k ^ 2 * I) - 6 * π * I * k * w) * thetaThree ν w := by
  unfold thetaThree
  rw [show 3 * (w + k * I) + ν * I = (3 * w + ν * I) + k * (3 * I) by ring, jacobiTheta₂_add_int_mul]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2; ring
end GroundTheory.Heights₂.Heights.KeyFormula

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_one_17c6616ebd0d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:05.571815+00:00
-- url     : https://prove2.me/submissions/1bbed406-d8fa-4333-9d3a-e05e6c5fcdb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_cadb2154e0f2


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
theorem _root_.solution (ν : ℕ) (w : ℂ) : thetaThree ν (w + 1) = thetaThree ν w := by
  unfold thetaThree
  rw [show 3 * (w + 1) + ν * I = (3 * w + ν * I) + ((3 : ℤ) : ℂ) by push_cast; ring,
    jacobiTheta₂_add_int]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨ν, by push_cast; ring⟩
end GroundTheory.Heights₂.Heights.KeyFormula

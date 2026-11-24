-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_cadb2154e0f2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:06.001563+00:00
-- url     : https://prove2.me/submissions/e5dc37f3-062d-46ed-8c81-95e2a1c69625

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial

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
open Complex Matrix Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (w τ : ℂ) (k : ℤ) : jacobiTheta₂ (w + k) τ = jacobiTheta₂ w τ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := jacobiTheta₂_add_left (w + k) τ
    push_cast at ih ⊢; rw [← add_assoc, this, ih]
  | pred k ih =>
    have := jacobiTheta₂_add_left (w + (-(k : ℂ) - 1)) τ
    push_cast at ih ⊢
    rw [show w + (-(k : ℂ) - 1) + 1 = w + -(k : ℂ) by ring] at this
    rw [← this, ih]
end GroundTheory.Heights₂.Heights.KeyFormula

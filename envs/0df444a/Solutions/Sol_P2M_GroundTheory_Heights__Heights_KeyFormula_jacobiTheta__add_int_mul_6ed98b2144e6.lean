-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_jacobiTheta__add_int_mul_6ed98b2144e6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:06.72679+00:00
-- url     : https://prove2.me/submissions/7813bbe4-13b9-4132-9cb1-149b5d3dadf5

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
theorem _root_.solution (w τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (w + k * τ) τ = cexp (-(π * I * k ^ 2 * τ) - 2 * π * I * k * w) * jacobiTheta₂ w τ := by
  induction k using Int.induction_on generalizing w with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show w + ((k : ℂ) + 1) * τ = (w + (k : ℂ) * τ) + τ by ring, jacobiTheta₂_add_left', ih,
      ← mul_assoc, ← Complex.exp_add]
    congr 1; ring_nf
  | pred k ih =>
    push_cast at ih ⊢
    have h := jacobiTheta₂_add_left' (w + (-(k : ℂ) - 1) * τ) τ
    rw [show w + (-(k : ℂ) - 1) * τ + τ = w + -(k : ℂ) * τ by ring, ih] at h
    have hne := Complex.exp_ne_zero (-π * I * (τ + 2 * (w + (-(k : ℂ) - 1) * τ)))
    rw [eq_comm, ← eq_inv_mul_iff_mul_eq₀ hne] at h
    rw [h, ← mul_assoc, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1; ring_nf
end GroundTheory.Heights₂.Heights.KeyFormula

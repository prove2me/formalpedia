-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_int_span_norm_ge_7217af94a27b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:24.669797+00:00
-- url     : https://prove2.me/submissions/8836d350-50e5-450f-be90-9d43f17ac7db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : ℝ) (hx : x ∈ Submodule.span ℤ ({1} : Set ℝ)) (h0 : x ≠ 0) :
    Real.exp (-0) ≤ ‖x‖ := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [neg_zero, Real.exp_zero, zsmul_eq_mul, mul_one, Real.norm_eq_abs]
  have ha : a ≠ 0 := by rintro rfl; simp at h0
  exact_mod_cast Int.one_le_abs ha
end GroundTheory.Heights₂.Heights

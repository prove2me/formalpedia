-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.exists_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:21:00.498335+00:00
-- url     : https://prove2.me/submissions/eb888c2a-3631-4cdd-b99f-7aabb65dbfc4

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
theorem _root_.solution {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (b : U →ₗ[ℝ] U →L[ℝ] ℝ)
    (hb : ∀ x, b x = 0 → x = 0) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, x ≠ 0 → ∃ a, ‖a‖ * ‖x‖ ≤ K ∧ b x a = 1 / 2 := by
  obtain ⟨K, -, hK⟩ := b.exists_antilipschitzWith (LinearMap.ker_eq_bot'.2 hb)
  refine ⟨K, K.2, fun x hx => ?_⟩
  have h0 : 0 < ‖b x‖ := norm_pos_iff.2 fun h => hx (hb x h)
  obtain ⟨a, ha, ha'⟩ := (b x).exists_lt_apply_of_lt_opNorm (half_lt_self h0)
  have h1 : b x a ≠ 0 := norm_pos_iff.1 (by linarith)
  have h2 : ‖x‖ ≤ K * ‖b x‖ := by simpa using hK.le_mul_dist x 0
  refine ⟨(2 * b x a)⁻¹ • a, ?_, by rw [map_smul, smul_eq_mul]; field_simp⟩
  rw [norm_smul, norm_inv, norm_mul, Real.norm_two, mul_assoc, inv_mul_le_iff₀ (by linarith)]
  have := K.2
  nlinarith [norm_nonneg a, norm_nonneg x, mul_nonneg this (norm_nonneg (b x a))]
end PositivityTheory.ThKCT.Arch

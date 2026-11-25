-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_rho_eq_zero_f7e1fc5f243f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:07.918005+00:00
-- url     : https://prove2.me/submissions/1c28543e-f386-4f7e-b852-1be707d6a1b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_nonneg_a601c8354dc1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
open GroundTheory.Heights₂.Heights.SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegrePartition
theorem _root_.solution (hN : 0 < numIdx ι) (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ)
    (h : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * ‖segre z‖) : rho i z = 0 := by
  have hδ : 0 < (Real.sqrt (2 * numIdx ι))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hw : 0 < ‖segre z‖ := by
    by_contra h0
    have : ‖segre z‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [this, mul_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg _))
  have hle : ‖segre z‖ ≤ Real.sqrt (segreSqSum z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun j => segreSq z j) (fun j _ => segreSq_nonneg z j)
      (Finset.mem_univ j)
  have hS : 0 < segreSqSum z := Real.sqrt_pos.mp (lt_of_lt_of_le hw hle)
  have h1 : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * Real.sqrt (segreSqSum z) :=
    lt_of_lt_of_le h (mul_le_mul_of_nonneg_left hle hδ.le)
  have h2 : segreSq z i < segreSqSum z / (2 * numIdx ι) := by
    have h3 := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hS.le] at h3
    rw [segreSq]
    calc ‖segre z i‖ ^ 2 < (2 * numIdx ι)⁻¹ * segreSqSum z := h3
      _ = segreSqSum z / (2 * numIdx ι) := by rw [inv_mul_eq_div]
  have hb : bump z i = 0 := by
    refine Real.smoothTransition.zero_of_nonpos ?_
    rw [lt_div_iff₀ (by positivity)] at h2
    have h4 : 2 * numIdx ι * (segreSq z i / segreSqSum z) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hS]
      linarith
    linarith
  simp only [rho, if_pos hS, hb, zero_div]
end GroundTheory.Heights₂.Heights.SegrePartition

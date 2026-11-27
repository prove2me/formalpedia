-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MonicRootGrowth_proof_aea245d3bb6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:02.157139+00:00
-- url     : https://prove2.me/submissions/4be884fb-f540-4ed0-838f-399b140974b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PMonicRootGrowth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_eval_le_sum_norm_coeff_mul_b54267a9929a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_le_one_add_sum_norm_coeff_of_monic_44e00fccf80b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace MonicRootGrowth
theorem _root_.solution : MonicRootGrowth.Statement := by
  intro d m hm
  set n := m.natDegree
  set S : ℕ → ℝ := fun i ↦ ∑ s ∈ (m.coeff i).support, ‖coeff s (m.coeff i)‖
  refine ⟨1 + ∑ i ∈ range n, S i, (range n).sup fun i ↦ (m.coeff i).totalDegree, fun y τ hτ ↦ ?_⟩
  have hmap : (m.map (eval y)).Monic := hm.map _
  have hdeg : (m.map (eval y)).natDegree = n := hm.natDegree_map _
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  set M := (range n).sup fun i ↦ (m.coeff i).totalDegree
  have hM : (1 : ℝ) ≤ (1 + ‖y‖) ^ M := one_le_pow₀ h1
  have hb := norm_le_one_add_sum_norm_coeff_of_monic hmap hτ
  rw [hdeg] at hb
  simp only [Polynomial.coeff_map] at hb
  calc ‖τ‖ ≤ 1 + ∑ i ∈ range n, ‖eval y (m.coeff i)‖ := hb
    _ ≤ 1 * (1 + ‖y‖) ^ M + ∑ i ∈ range n, S i * (1 + ‖y‖) ^ M := by
        gcongr with i hi
        · simpa using hM
        · refine (norm_eval_le_sum_norm_coeff_mul _ y).trans ?_
          gcongr
          exact le_sup (f := fun i ↦ (m.coeff i).totalDegree) hi
    _ = (1 + ∑ i ∈ range n, S i) * (1 + ‖y‖) ^ M := by rw [add_mul, sum_mul]
end MonicRootGrowth
end GroundTheory.Heights₂.Heights.HilbertSamuel

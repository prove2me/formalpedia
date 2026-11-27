-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_Halving_proof_972cfc07e2fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:46.753265+00:00
-- url     : https://prove2.me/submissions/a0161178-9d80-46bc-aa21-429c9768cda4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHalving
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_Halving_eventually_le_124ebeeb4013

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
open Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace Halving
theorem _root_.solution : Halving.Statement := by
  intro a ⟨C, hC⟩ hh hs
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C / 2 ^ k < ε / 2 := by
    have ht : Tendsto (fun k : ℕ ↦ C / 2 ^ k) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, ← inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num)).const_mul C
    exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).exists
  obtain ⟨N, hN⟩ := Halving.eventually_le a C hC hh hs k (ε / 4) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero]
  linarith [hN n hn]
end Halving
end GroundTheory.Heights₂.Heights.HilbertSamuel

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolyNonvanishDense_proof_de87f7ac635d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:20.936111+00:00
-- url     : https://prove2.me/submissions/a7ca4b14-61df-41e4-9ef8-90f787b127c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonvanishDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolyNonvanishDense

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PolyNonvanishDense
theorem _root_.solution : PolyNonvanishDense.Statement := by
  intro e D hD
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  have hzero : map (algebraMap ℚ ℂ) D = 0 := by
    refine funext_set (fun j => Metric.ball (y₀ j) ε)
      (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_
    rw [← ball_pi y₀ hε] at hy
    have hyU := hball hy
    rw [map_zero, eval_map, ← aeval_def]
    by_contra hyD
    exact (Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hyU, hyD⟩
  exact hD (map_injective _ (algebraMap ℚ ℂ).injective (by rw [hzero, map_zero]))
end PolyNonvanishDense
end GroundTheory.Heights₂.Heights.HilbertSamuel

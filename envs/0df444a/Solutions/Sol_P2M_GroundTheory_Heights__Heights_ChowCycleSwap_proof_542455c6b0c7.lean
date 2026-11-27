-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowCycleSwap_proof_542455c6b0c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:06:04.805273+00:00
-- url     : https://prove2.me/submissions/aa86d977-d58d-4688-956c-d74465449ebf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowCycleSwap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowFormSwap_457535a64ce2


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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChowCycleSwap
theorem _root_.solution : ChowCycleSwap.Statement := by
  intro F _ n k Z f hf τ
  obtain ⟨c, -, g, hg, rfl⟩ := hf
  have hex : ∀ W, ∃ d : F, W ∈ Z.support →
      d ^ 2 = 1 ∧ rename (Prod.map τ id) (g W) = C d * g W := by
    intro W
    by_cases hW : W ∈ Z.support
    · obtain ⟨d, hd2, hdg⟩ := chowFormSwap F n k W (g W) (hg W hW) τ
      exact ⟨d, fun _ => ⟨hd2, hdg⟩⟩
    · exact ⟨1, fun h => absurd h hW⟩
  choose d hd using hex
  refine ⟨∏ W ∈ Z.support, d W ^ Z W, ?_, ?_⟩
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun W hW => ?_
    rw [← pow_mul, mul_comm, pow_mul, (hd W hW).1, one_pow]
  · rw [map_mul, rename_C, map_prod]
    rw [Finset.prod_congr rfl fun W hW => by
      rw [map_pow, (hd W hW).2, mul_pow, ← C_pow]]
    rw [Finset.prod_mul_distrib, map_prod C]
    ring
end ChowCycleSwap
end GroundTheory.Heights₂.Heights

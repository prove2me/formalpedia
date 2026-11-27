-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpecFirstHomog_proof_176a5a02313b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:04.852413+00:00
-- url     : https://prove2.me/submissions/4b885ac5-360e-49db-84b3-c7e54b7fa712

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSpecFirstHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirstVar_isWeightedHomogeneous_3ddffe640504

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
namespace GroundTheory.Heights₂.Heights
namespace SpecFirstHomog
theorem _root_.solution : SpecFirstHomog.Statement := by
  intro n k δ f u hf
  unfold IsMultiHomog specFirst
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous u ij).pow _
end SpecFirstHomog
end GroundTheory.Heights₂.Heights

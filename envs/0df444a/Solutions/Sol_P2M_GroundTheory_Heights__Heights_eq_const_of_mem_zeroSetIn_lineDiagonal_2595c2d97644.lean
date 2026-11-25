-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eq_const_of_mem_zeroSetIn_lineDiagonal_2595c2d97644
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:36.297254+00:00
-- url     : https://prove2.me/submissions/3cb6bfff-d65d-4d2a-ae26-51660cc40842

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint

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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {z : Fin 1 ⊕ Fin 1 → ℂ}
    (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalIdeal) :
    z = fun _ => z (Sum.inl 0) := by
  have hzd : z (Sum.inr 0) = z (Sum.inl 0) := by
    have h1 := hz (X (Sum.inr 0) - X (Sum.inl 0)) (by
      show IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalMap (X (Sum.inr 0) - X (Sum.inl 0)) = 0
      rw [IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalMap, map_sub, aeval_X, aeval_X]
      simp)
    simp only [map_sub, eval_X] at h1
    exact sub_eq_zero.mp h1
  funext s
  rcases s with i | i
  · rw [Subsingleton.elim i 0]
  · rw [Subsingleton.elim i 0, hzd]
end GroundTheory.Heights₂.Heights

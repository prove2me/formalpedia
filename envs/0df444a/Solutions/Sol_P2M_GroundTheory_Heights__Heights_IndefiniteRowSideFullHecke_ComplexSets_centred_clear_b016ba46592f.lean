-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centred_clear_b016ba46592f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:26.677089+00:00
-- url     : https://prove2.me/submissions/a3ca8c0a-bdb2-481f-be93-bd7b20c42938

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitivePresentationCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pow_clear_a8cd4d5a4e47

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n : ℕ} (b : Fin n → ℂ) (M : ℕ) (e x : ℂ) :
    (e ^ M * x) ^ n + ∑ j, b j * e ^ (M * (n - j)) * (e ^ M * x) ^ (j : ℕ) =
      e ^ (M * n) * (x ^ n + ∑ j, b j * x ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, mul_pow, ← pow_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, pow_clear _ _ _ _ _ j.2.le]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

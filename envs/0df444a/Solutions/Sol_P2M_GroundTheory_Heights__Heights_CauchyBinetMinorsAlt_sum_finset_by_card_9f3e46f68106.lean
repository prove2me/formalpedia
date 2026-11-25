-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_finset_by_card_9f3e46f68106
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:33.898441+00:00
-- url     : https://prove2.me/submissions/4ad054e5-8d65-4006-ad69-1fe56a984237

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors

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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
namespace GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
theorem _root_.solution {n : ℕ} {β : Type*} [AddCommMonoid β] (f : Finset (Fin n) → β) :
    ∑ s : Finset (Fin n), f s =
      ∑ k ∈ range (n + 1), ∑ S : {S : Finset (Fin n) // S.card = k}, f S.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1)) (fun s _ => by
    have := card_le_univ s
    simp only [Fintype.card_fin] at this
    exact mem_range.2 (by omega))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_subtype _ (fun s => by simp) _
end GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt

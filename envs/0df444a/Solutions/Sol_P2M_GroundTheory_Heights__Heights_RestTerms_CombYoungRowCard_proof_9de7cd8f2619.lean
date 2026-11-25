-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombYoungRowCard_proof_9de7cd8f2619
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:19.544523+00:00
-- url     : https://prove2.me/submissions/4251de1d-3141-4fba-97b6-77b5304bef4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombYoungRowCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombYoungRowCard
theorem _root_.solution : CombYoungRowCard.Statement := by
  intro m lam i
  rw [← Finset.card_range (lam i)]
  refine Finset.card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hc : p.1.2 < lam p.1.1 := (mem_filter.1 p.2).2
    rw [hp'] at hc
    exact mem_range.2 hc
  · intro p hp q hq h
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hq' : q.1.1 = i := (mem_filter.1 hq).2
    exact Subtype.ext (Prod.ext (hp'.trans hq'.symm) h)
  · intro c hc
    have hc' : c < lam i := mem_range.1 hc
    have hmem : ((i, c) : Fin m × ℕ) ∈ youngCells lam := by
      unfold youngCells
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_range.2 ?_⟩, hc'⟩
      exact lt_of_lt_of_le hc'
        (Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (mem_univ i))
    exact ⟨⟨(i, c), hmem⟩, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩
end CombYoungRowCard
end GroundTheory.Heights₂.Heights.RestTerms

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_strictMono_aeabc6a5e861
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:35.836744+00:00
-- url     : https://prove2.me/submissions/90fd4912-c16e-4761-b93b-bc2686bc8796

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
theorem _root_.solution {n k : ℕ} {β : Type*} [AddCommMonoid β]
    [DecidablePred (fun b : Fin k → Fin n => StrictMono b)] (g : (Fin k → Fin n) → β) :
    ∑ b ∈ univ.filter (fun b : Fin k → Fin n => StrictMono b), g b =
      ∑ S : {S : Finset (Fin n) // S.card = k}, g (S.1.orderEmbOfFin S.2) := by
  symm
  refine Finset.sum_bij (fun S _ => (S.1.orderEmbOfFin S.2 : Fin k → Fin n)) ?_ ?_ ?_ ?_
  · intro S _
    simpa using (S.1.orderEmbOfFin S.2).strictMono
  · intro S _ T _ h
    apply Subtype.ext
    have h' := congrArg Set.range h
    simp only [range_orderEmbOfFin] at h'
    exact_mod_cast h'
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    have hc : (univ.image b).card = k := by
      rw [card_image_of_injective _ hb.injective, card_univ, Fintype.card_fin]
    exact ⟨⟨univ.image b, hc⟩, mem_univ _,
      (orderEmbOfFin_unique hc (fun x => mem_image_of_mem b (mem_univ x)) hb).symm⟩
  · intro _ _
    rfl
end GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt

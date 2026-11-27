-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleConnected_proof_ff3de10b6417
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:27.131897+00:00
-- url     : https://prove2.me/submissions/70c8d904-73a2-4c82-80af-15b315fc03d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StatementsBasicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIrreducibleConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleConnected_exists_ne_zero_7c26e2820178

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
namespace IrreducibleConnected
theorem _root_.solution (hB : IrreducibleBasicOpenConnected.Statement) :
    IrreducibleConnected.Statement := by
  intro σ _ W J hW
  set D : MvPolynomial σ ℂ → Set (σ → ℂ) := fun g => zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0} with hD
  have hU : zeroLocus ℂ W \ zeroLocus ℂ J = ⋃ g ∈ {g | g ∈ J ∧ g ∉ W}, D g := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, hD, mem_zeroLocus_iff,
      exists_prop]
    constructor
    · rintro ⟨hxW, hxJ⟩
      push Not at hxJ
      obtain ⟨g, hgJ, hg⟩ := hxJ
      exact ⟨g, ⟨hgJ, fun hgW => hg (hxW g hgW)⟩, hxW, hg⟩
    · rintro ⟨g, ⟨hgJ, -⟩, hxW, hg⟩
      exact ⟨hxW, fun h => hg (h g hgJ)⟩
  rw [hU]
  refine IsPreconnected.biUnion_of_reflTransGen (fun g hg => hB σ W g hW hg.2) ?_
  intro g hg g' hg'
  refine Relation.ReflTransGen.single ⟨?_, hg⟩
  have hgg' : g * g' ∉ W := fun hm => (hW.mem_or_mem hm).elim hg.2 hg'.2
  obtain ⟨x, hxW, hx⟩ := IrreducibleConnected.exists_ne_zero hW hgg'
  rw [map_mul] at hx
  exact ⟨x, ⟨hxW, left_ne_zero_of_mul hx⟩, ⟨hxW, right_ne_zero_of_mul hx⟩⟩
end IrreducibleConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel

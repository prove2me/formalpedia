-- Prove2me | solution 1 for PI.KLW.Ind.spans_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:44:40.565054+00:00
-- url     : https://prove2.me/submissions/c10d6a7c-7859-46ef-bb1a-dedb25ebdf78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] {ι : Type} {σ : (ι → K) ≃ₗ[K] (ι → K)}
    {L : Set (ι → K)} (hS : Spans K L) : Spans K (σ ⁻¹' L) := fun v => by
  obtain ⟨N, hN, h⟩ := hS (σ v)
  exact ⟨N, hN, by show σ _ ∈ L; rw [map_smul]; exact h⟩
end PI.KLW.Ind

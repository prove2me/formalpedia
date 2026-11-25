-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_restPsumIdeal_generators_eq_range_4c5aec6134c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:03.903172+00:00
-- url     : https://prove2.me/submissions/025c6f6e-e40e-47ff-a881-ad6578c91e8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIdealSum

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
theorem _root_.solution (f N : ℕ) :
    {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = RestTerms.blockPowerSum f N k τ} =
      Set.range fun i : Fin N × Fin f => RestTerms.blockPowerSum f N ((i.1 : ℕ) + 1) i.2 := by
  ext P
  constructor
  · rintro ⟨k, τ, hk1, hkN, rfl⟩
    refine ⟨(⟨k - 1, by omega⟩, τ), ?_⟩
    simp only
    congr 1
    omega
  · rintro ⟨i, rfl⟩
    exact ⟨(i.1 : ℕ) + 1, i.2, by omega, by omega, rfl⟩
end GroundTheory.Heights₂.Heights

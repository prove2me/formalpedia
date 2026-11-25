-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_proof_254c61677cca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:01.480732+00:00
-- url     : https://prove2.me/submissions/aa8e4b95-acb2-408f-8991-c05b9b05def3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_X_sub_1f06c67bc04a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_eq_zero_of_dvd_cecf2aecafc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_of_collapse_eq_zero_1f3904f429e5

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
variable {σ : Type} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
theorem _root_.solution : FlagDiffPrime.Statement := by
  intro σ _ a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_ne_zero]
    exact fun h => hab (X_injective h)
  · intro hu
    have hu' := hu.map (collapse a b)
    rw [collapse_X_sub] at hu'
    exact not_isUnit_zero hu'
  · intro A B h
    have h0 := collapse_eq_zero_of_dvd a b h
    rw [map_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Or.inl (dvd_of_collapse_eq_zero a b h0)
    · exact Or.inr (dvd_of_collapse_eq_zero a b h0)
end GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime

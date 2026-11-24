-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:12.729033+00:00
-- url     : https://prove2.me/submissions/b0e3e18d-7a91-47e8-9130-4cbaf9d6fdcd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [∀ k, Nonempty (ι k)] :
    IsMultiProjPrime (⊥ : Ideal (MRing ι R)) where
  isPrime := Ideal.isPrime_bot
  multiHomog := by
    intro f hf b
    rw [Ideal.mem_bot] at hf ⊢
    simp [hf]
  relevant := by
    intro k
    refine ⟨Classical.arbitrary _, ?_⟩
    rw [Ideal.mem_bot]
    exact X_ne_zero _
end GroundTheory.Heights₂.Heights.NumbersDVR

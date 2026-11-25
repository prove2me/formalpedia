-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_mem_minimalPrimes_iff_5f70c654c603
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:26.789925+00:00
-- url     : https://prove2.me/submissions/59c29157-f6be-4aa5-ba24-e0879792b3e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

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
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {S : Type*} [CommRing S]
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {J J₁ W : Ideal S} (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) : W ∈ J.minimalPrimes ↔ W ∈ J₁.minimalPrimes := by
  have key : ∀ Q : Ideal S, Q.IsPrime → Q ≤ W → (J ≤ Q ↔ J₁ ≤ Q) := fun Q hQ hQW ↦
    ⟨fun h x hx ↦ (hQ.mem_or_mem (h (hmul x hx))).resolve_left fun htQ ↦ ht (hQW htQ), hJ.trans⟩
  simp only [Ideal.minimalPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mp hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mpr hQ.2⟩ hQW⟩
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mpr hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mp hQ.2⟩ hQW⟩
end GroundTheory.Heights₂.Heights.SectionCycle

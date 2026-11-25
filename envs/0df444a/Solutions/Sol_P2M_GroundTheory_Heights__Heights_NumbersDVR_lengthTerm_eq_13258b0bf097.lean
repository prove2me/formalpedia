-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthTerm_eq_13258b0bf097
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:15.5957+00:00
-- url     : https://prove2.me/submissions/dd99976e-177f-4ba3-b47c-2a312024a0ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ordMod_eq_length_quot_sup_1026a45f8ec3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_eq_zero_of_notMem


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
open Module IsLocalRing ReciprocityTheory.ChartRestriction.G.AI
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (hdim : ringKrullDim A = 1) (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (x : A) (p : PrimeSpectrum A) :
    (∑ᶠ (_ : ringKrullDim (A ⧸ p.asIdeal) = 1),
        length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
          ordMod p x) =
      ∑ᶠ (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes ∧
          p.asIdeal ≠ maximalIdeal A),
        length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
          length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x})) := by
  classical
  have hiff := dim_quot_eq_one_iff hdim p.asIdeal
  rw [ordMod_eq_length_quot_sup, finsum_eq_if, finsum_eq_if]
  by_cases hm : p.asIdeal.IsMaximal
  · rw [if_neg (fun h => hiff.mp h hm), if_neg (fun h => h.2 (eq_maximalIdeal hm))]
  · have hne : p.asIdeal ≠ maximalIdeal A := fun h => hm (h ▸ maximalIdeal.isMaximal A)
    rw [if_pos (hiff.mpr hm)]
    by_cases hle : Module.annihilator A M ≤ p.asIdeal
    · have hmin : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes :=
        ⟨⟨p.isPrime, hle⟩, fun q hq hqp => by
          have := hq.1
          exact (eq_of_not_max_of_le hdim hm hqp).le⟩
      rw [if_pos ⟨hmin, hne⟩]
    · rw [if_neg (fun h => hle h.1.le)]
      have h0 := locLen_eq_zero_of_notMem (N := M) p
        (by rw [Module.mem_support_iff_of_finite]; exact hle)
      unfold locLen at h0
      rw [h0, zero_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR

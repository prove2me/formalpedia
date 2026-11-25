-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_eq_of_mul_le_8d87d4368795
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:23.387804+00:00
-- url     : https://prove2.me/submissions/3ed7c2b2-e918-4043-9fb0-3f10bcc04f6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {I J W : Ideal A} [W.IsPrime] (hIJ : I ≤ J) {s : A}
    (hs : s ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ I) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ I)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) := by
  let q : (A ⧸ I) →ₗ[A] A ⧸ J := Submodule.mapQ _ _ LinearMap.id (fun a ha => hIJ ha)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  let f₁ := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ I)
  let f₂ := LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J)
  let φ := IsLocalizedModule.map W.primeCompl f₁ f₂ q
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_localizedMap_eq_localized₀_ker, eq_bot_iff]
    intro z hz
    rw [Submodule.mem_localized₀] at hz
    obtain ⟨m, hm, t, ht, rfl⟩ := hz
    rw [Submodule.mem_bot, IsLocalizedModule.mk'_eq_zero']
    refine ⟨⟨s, hs⟩, ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    have hxJ : x ∈ J := (Submodule.Quotient.mk_eq_zero _).mp hm
    change Submodule.Quotient.mk (s • x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hsJ x hxJ)
  let e : LocalizedModule W.primeCompl (A ⧸ I) ≃ₗ[A] LocalizedModule W.primeCompl (A ⧸ J) :=
    LinearEquiv.ofBijective φ ⟨hinj, IsLocalizedModule.map_surjective _ _ _ q hq⟩
  exact (e.extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)).length_eq
end GroundTheory.Heights₂.Heights.NumbersDVR

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_mul_mul_0239d507d543
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:01.930156+00:00
-- url     : https://prove2.me/submissions/015f5ef6-9be8-43c6-ae18-00c75c4f869a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe

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
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
theorem _root_.solution (hmul : DivCycleMul.Statement.{u}) {O : Type u} [CommRing O] [IsNoetherianRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    {f₁ g₁ f₂ g₂ : MRing ι O} (hf₁ : f₁ ∉ P) (hf₂ : f₂ ∉ P) (hg₁ : g₁ ∉ P) (hg₂ : g₂ ∉ P) :
    ratDiv P (f₁ * f₂) (g₁ * g₂) = ratDiv P f₁ g₁ + ratDiv P f₂ g₂ := by
  funext W
  simp only [ratDiv, Pi.add_apply, hmul O K ι P f₁ f₂ hP hf₁ hf₂, hmul O K ι P g₁ g₂ hP hg₁ hg₂]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor

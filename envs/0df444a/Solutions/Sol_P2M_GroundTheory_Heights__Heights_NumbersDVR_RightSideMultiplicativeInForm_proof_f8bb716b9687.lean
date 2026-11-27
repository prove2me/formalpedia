-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_RightSideMultiplicativeInForm_proof_f8bb716b9687
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:39.168437+00:00
-- url     : https://prove2.me/submissions/d06e7b09-2722-4049-9b14-8da5079fa1a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalAddOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
private theorem cycEval_add_of_finite {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (φ : Ideal (MRing ι R) → ℤ) {Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite) :
    cycEval φ (Z₁ + Z₂) = cycEval φ Z₁ + cycEval φ Z₂ := by
  unfold cycEval
  have f₁ : (Function.support fun W => Z₁ W * φ W).Finite :=
    h₁.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => Z₂ W * φ W).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [← finsum_add_distrib f₁ f₂]
  refine finsum_congr fun W => ?_
  simp only [Pi.add_apply]
  ring
end
end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace RightSideMultiplicativeInForm
theorem _root_.solution (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : RightSideMultiplicativeInForm.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g s₁ s₂ hs₁ hs₂ L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cutIdentityRightSide
  rw [h₁ O K ι P s₁ s₂ hPp hs₁ hs₂]
  exact cycEval_add_of_finite _ (h₂ O K ι P s₁) (h₂ O K ι P s₂)
end RightSideMultiplicativeInForm
end GroundTheory.Heights₂.Heights.NumbersDVR

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveNormalisationLength_hypotheses_inhabited_53fb645db4c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:59.768865+00:00
-- url     : https://prove2.me/submissions/3f817a24-4542-45bf-8f47-2c8eaf76df0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_curveLocalRing_line_968c08547264
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRadicalAt_of_isRadical_90f13697c733


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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace CurveNormalisationLength
theorem _root_.solution :
    IsRadicalAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0 ∧
      ringKrullDim (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) = 1 ∧
      algebraMap (MvPolynomial (Fin 1) ℂ) (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) (X 0) ∈
        nonZeroDivisors (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) := by
  refine ⟨isRadicalAt_of_isRadical Ideal.isPrime_bot.isRadical 0, ringKrullDim_curveLocalRing_line, ?_⟩
  have : IsDomain (curveLocalRing (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 0) :=
    curveLocalRingLineEquiv.toMulEquiv.isDomain
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ ?_
  have h' := congrArg curveLocalRingLineEquiv h
  rw [map_zero] at h'
  have hinj := IsLocalization.injective (Localization.AtPrime (RingHom.ker (eval (0 : Fin 1 → ℂ))))
    (M := (RingHom.ker (eval (0 : Fin 1 → ℂ))).primeCompl)
    (Ideal.primeCompl_le_nonZeroDivisors _)
  apply X_ne_zero (R := ℂ) (0 : Fin 1)
  apply hinj
  rw [map_zero]
  exact h'
end CurveNormalisationLength
end GroundTheory.Heights₂.Heights

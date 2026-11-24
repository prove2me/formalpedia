-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PolynomialPrimeOverZeroHeight_proof_17c289546d57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:05.081876+00:00
-- url     : https://prove2.me/submissions/83073468-6eba-4273-9a3d-af5bc5ad75ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialPrimeOverZeroHeight

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
open Polynomial
attribute [local instance] Polynomial.algebra Polynomial.isLocalization
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace PolynomialPrimeOverZeroHeight
theorem _root_.solution : PolynomialPrimeOverZeroHeight.Statement := by
  intro D _ _ Q _ hQ
  let K := FractionRing D
  have disj : Disjoint ((nonZeroDivisors D).map (C : D →+* D[X]) : Set D[X]) (Q : Set D[X]) := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ ?_
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb.1
    apply hb0
    have : b ∈ Q.comap (C : D →+* D[X]) := by
      rw [Ideal.mem_comap]
      simpa [hb.2] using ha
    rwa [hQ, Ideal.mem_bot] at this
  have hK : ringKrullDim K[X] = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)
  have h := IsLocalization.height_map_of_disjoint ((nonZeroDivisors D).map (C : D →+* D[X]))
    (S := K[X]) Q disj
  have hP : (Q.map (algebraMap D[X] K[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors D).map (C : D →+* D[X])) K[X] Q
      ‹_› disj
  have hle : ((Q.map (algebraMap D[X] K[X])).height : WithBot ℕ∞) ≤ 1 :=
    hK ▸ Ideal.height_le_ringKrullDim_of_isPrime
  rw [h] at hle
  exact_mod_cast hle
end PolynomialPrimeOverZeroHeight
end GroundTheory.Heights₂.Heights.NumbersDVR

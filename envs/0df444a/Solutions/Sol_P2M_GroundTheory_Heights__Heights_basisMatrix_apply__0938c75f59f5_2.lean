-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_basisMatrix_apply__0938c75f59f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:59.853182+00:00
-- url     : https://prove2.me/submissions/6ad4c166-c718-4f27-a401-23d0bbf05327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module
open scoped Kronecker
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (τ σ : K →+* ℂ) :
    basisMatrix K τ σ = σ ((RingOfIntegers.basis K (equivReindex K τ) : 𝓞 K) : K) := by
  simp [basisMatrix, canonicalEmbedding.latticeBasis_apply, integralBasis_apply,
    canonicalEmbedding.apply_at]
end GroundTheory.Heights₂.Heights

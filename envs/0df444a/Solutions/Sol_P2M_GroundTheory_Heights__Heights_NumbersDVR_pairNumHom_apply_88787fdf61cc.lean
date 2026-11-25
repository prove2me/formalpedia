-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNumHom_apply_88787fdf61cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:00.310348+00:00
-- url     : https://prove2.me/submissions/8296c6c4-5f8f-4840-b186-6a848ce7168d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {n : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin n → K → ℤ)
    (f g : Fin n → MRing ι O) (Q : List (K → ℤ)) (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    pairNumHom P x x' f g Q Gs = pairNum P x x' f g Gs Q := rfl
end GroundTheory.Heights₂.Heights.NumbersDVR

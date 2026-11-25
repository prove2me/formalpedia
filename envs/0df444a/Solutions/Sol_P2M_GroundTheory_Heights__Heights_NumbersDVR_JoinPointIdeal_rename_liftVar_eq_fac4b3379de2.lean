-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_rename_liftVar_eq_fac4b3379de2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:27.255063+00:00
-- url     : https://prove2.me/submissions/83cfd2ff-3c7e-4fa4-84bd-e311a7e08e85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinPointIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinPointIdeal

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar joinCoord mcIdeal mcMap)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointIdeal
noncomputable section
variable {K : Type} {ι : K → Type}
variable (R : Type) [CommRing R]
variable (Ω : Type) [Field Ω] [Algebra R Ω]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointIdeal
theorem _root_.solution :
    ((rename (liftVar (ι := ι) ptIdx) : MRing ι R →ₐ[R] MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) :
        MRing ι R →+* MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R) =
      ((srcEquiv (ι := ι) R).symm : MvPolynomial Unit (MRing ι R) →+* _).comp
        (C : MRing ι R →+* MvPolynomial Unit (MRing ι R)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [srcEquiv]
  · intro p
    simp [srcEquiv, liftVar, joinIdx]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointIdeal

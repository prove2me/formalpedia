-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_tgtEquiv_mcMap_818d2f828477
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:49.190559+00:00
-- url     : https://prove2.me/submissions/b85761e1-0c78-4ded-aac4-8a711e60a868

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel
theorem _root_.solution (y : (Σ k, ι k) → Ω) (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    tgtEquiv K Ω (mcMap O (joinCoord y (ptCoord (Ω := Ω))) p) =
      Polynomial.map (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω) (srcEquiv O p) := by
  have h : ((tgtEquiv K Ω : MvPolynomial (K ⊕ Unit) Ω →+* Polynomial (MvPolynomial K Ω)).comp
      (mcMap O (joinCoord y (ptCoord (Ω := Ω))) : _ →+* MvPolynomial (K ⊕ Unit) Ω)) =
      (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)).comp
        (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tgtEquiv, srcEquiv, mcMap, optionEquivLeft_C]
    · rintro ⟨k | u, i⟩
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, optionEquivLeft_X_some, optionEquivLeft_C]
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, ptCoord, optionEquivLeft_X_none]
  exact RingHom.congr_fun h p
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointModel

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ProjectiveBundleNumbers_hyp_inhabited_b5287fa021f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:59:31.587481+00:00
-- url     : https://prove2.me/submissions/432b48fa-c5af-4f1b-8a09-c78e22b874e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_trivBundle_isFlagGrading_b44ce4708f58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_trivBundle_isTwistedForms_f9e1790831e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ker_genPt_faef97509c8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isProjVarF_line_922058d2e971

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w u₁ u₂
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {o}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
namespace ProjectiveBundleNumbers
theorem _root_.solution (F : Type*) [Field F] :
    IsProjVarF (⊥ : Ideal (MRingOver F (fun _ : Unit => Fin 2))) 1 ∧
      RingHom.ker (genPt F (fun _ : Unit => Fin 2)) = ⊥ ∧ 1 ≤ 2 ∧
      IsFlagGrading (genPt F (fun _ : Unit => Fin 2))
        (trivBundle F (segreVec (genPt F (fun _ : Unit => Fin 2))) 2) (Pi.basisFun _ (Fin 2)) 0 1 ∧
      IsTwistedForms (genPt F (fun _ : Unit => Fin 2))
        (trivBundle F (segreVec (genPt F (fun _ : Unit => Fin 2))) 2)
        (fun t : Fin 2 => (LinearMap.proj t : (Fin 2 → _) →ₗ[_] _)) 0 ∧ 1 ≤ 2 - 1 + 1 :=
  ⟨isProjVarF_line F, ker_genPt F, by norm_num, trivBundle_isFlagGrading _ 2,
    trivBundle_isTwistedForms _ 2, by norm_num⟩
end ProjectiveBundleNumbers
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

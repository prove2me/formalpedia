-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_TwoExpansionsAgree_hyp_inhabited_146b61f05b4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:59:36.804851+00:00
-- url     : https://prove2.me/submissions/4dea8369-cfc0-48b2-b8c9-15ea66412129

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ker_genPt_faef97509c8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_trivBundle_isFlagPair_fa4d0d68530e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isHomogeneous_esymm_int_41d27f636aff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isModelOver_line_c8d82f335840


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
namespace TwoExpansionsAgree
theorem _root_.solution :
    Irreducible ((2 : ℕ) : ℤ_[2]) ∧
      IsModelOver (⊥ : Ideal (MRingOver ℤ_[2] (fun _ : Unit => Fin 2))) 1 ∧
      RingHom.ker (genPt ℤ_[2] (fun _ : Unit => Fin 2)) = ⊥ ∧
      SameGenericFibre ((2 : ℕ) : ℤ_[2])
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2) ∧
      IsFlagPair (genPt ℤ_[2] (fun _ : Unit => Fin 2)) ⊥
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (trivBundle ℤ_[2] (segreVec (genPt ℤ_[2] (fun _ : Unit => Fin 2))) 2)
        (Pi.basisFun _ (Fin 2)) 0 0 1 1 1 1 ∧
      (esymm (Fin 2) ℤ 2).IsSymmetric ∧ (esymm (Fin 2) ℤ 2).IsHomogeneous (1 + 1) :=
  ⟨PadicInt.irreducible_p, isModelOver_line ℤ_[2], ker_genPt ℤ_[2],
    fun _ _ _ => Iff.rfl, trivBundle_isFlagPair 2, esymm_isSymmetric _ _ _,
    isHomogeneous_esymm_int _ 2⟩
end TwoExpansionsAgree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

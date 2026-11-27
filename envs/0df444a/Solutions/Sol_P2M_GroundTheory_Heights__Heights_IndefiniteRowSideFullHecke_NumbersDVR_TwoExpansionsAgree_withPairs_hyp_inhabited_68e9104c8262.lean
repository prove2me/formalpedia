-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_TwoExpansionsAgree_withPairs_hyp_inhabited_68e9104c8262
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:59:45.824077+00:00
-- url     : https://prove2.me/submissions/3964cef2-c191-4259-8503-490d6fe84844

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isHomogeneous_esymm_int_41d27f636aff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isVerticalDiv_unif_ff6fcf4a766b


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
    IsVerticalDiv ((2 : ℕ) : ℤ_[2]) (⊥ : Ideal (MRingOver ℤ_[2] (fun _ : Unit => Fin 2)))
        (unifPair (ι := fun _ : Unit => Fin 2) ((2 : ℕ) : ℤ_[2])).b
        (unifPair (ι := fun _ : Unit => Fin 2) ((2 : ℕ) : ℤ_[2])).f
        (unifPair (ι := fun _ : Unit => Fin 2) ((2 : ℕ) : ℤ_[2])).g ∧
      1 ≤ 1 + 1 ∧ (esymm (Fin 2) ℤ 1).IsSymmetric ∧ (esymm (Fin 2) ℤ 1).IsHomogeneous (1 + 1 - 1) :=
  ⟨isVerticalDiv_unif _ Ideal.isPrime_bot, by norm_num, esymm_isSymmetric _ _ _,
    isHomogeneous_esymm_int _ 1⟩
end TwoExpansionsAgree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

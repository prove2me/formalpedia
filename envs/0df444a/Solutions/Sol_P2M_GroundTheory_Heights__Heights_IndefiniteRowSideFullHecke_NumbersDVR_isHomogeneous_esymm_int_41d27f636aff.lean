-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isHomogeneous_esymm_int_41d27f636aff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:56.472168+00:00
-- url     : https://prove2.me/submissions/76f94f0a-d6fa-4360-a5a2-e542d44f6e18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms

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
theorem _root_.solution (σ : Type*) [Fintype σ] (n : ℕ) :
    (esymm σ ℤ n).IsHomogeneous n := by
  unfold esymm
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have := IsHomogeneous.prod t (fun i => (X i : MvPolynomial σ ℤ)) (fun _ => 1)
    fun i _ => isHomogeneous_X ℤ i
  simpa [(Finset.mem_powersetCard.1 ht).2] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

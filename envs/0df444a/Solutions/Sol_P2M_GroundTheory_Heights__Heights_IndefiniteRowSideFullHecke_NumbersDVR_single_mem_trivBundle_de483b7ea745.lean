-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_single_mem_trivBundle_de483b7ea745
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:58.387127+00:00
-- url     : https://prove2.me/submissions/e1f9a4e5-83e6-48c5-b13a-b3c7f77f0718

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_mem_trivBundle_251b4824d13c

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
theorem _root_.solution {ι' : Type*} {x : ι' → Ω} {N : ℕ} {i : ι'} (l : Fin N) {r : Ω}
    (hr : r ∈ chartRing o x i) : Pi.single l r ∈ (trivBundle o x N).lat i := by
  refine mem_trivBundle.2 fun q => ?_
  by_cases h : q = l
  · subst h
    simpa using hr
  · simp [h, zero_mem]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

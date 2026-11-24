-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_chartMono_zero_1b1fcd88d57b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:56.052446+00:00
-- url     : https://prove2.me/submissions/47ca7f61-4d77-4717-afd0-de376a56c6ce

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
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution (pt : MRingOver o ι →ₐ[o] Ω) (i : (k : K) → ι k) : chartMono pt i 0 = 1 := by
  simp [chartMono]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

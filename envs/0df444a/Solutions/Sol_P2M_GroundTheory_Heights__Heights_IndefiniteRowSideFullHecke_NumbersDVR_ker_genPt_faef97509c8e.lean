-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_ker_genPt_faef97509c8e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:57.692852+00:00
-- url     : https://prove2.me/submissions/915b0b4e-1921-48b0-9568-0f5f56fa69e6

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
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution (R : Type*) [CommRing R] [IsDomain R] :
    RingHom.ker (genPt R ι) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective _ _)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

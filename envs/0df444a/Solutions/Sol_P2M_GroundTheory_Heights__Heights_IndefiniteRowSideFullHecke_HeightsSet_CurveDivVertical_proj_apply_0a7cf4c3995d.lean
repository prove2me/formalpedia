-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_proj_apply_0a7cf4c3995d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.083973+00:00
-- url     : https://prove2.me/submissions/310aa412-942a-4e5e-8c55-e5613a9aac06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
theorem _root_.solution (T : Finset K) (f : MRing ι) :
    proj T f = weightedHomogeneousComponent (wt T) 0 f := by
  rw [proj, GradedRing.projZeroRingHom_apply]
  exact weightedDecomposition.decompose'_apply ℤ (wt T) f 0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical

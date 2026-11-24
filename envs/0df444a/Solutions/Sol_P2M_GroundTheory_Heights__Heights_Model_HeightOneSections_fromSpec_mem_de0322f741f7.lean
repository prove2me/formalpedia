-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_fromSpec_mem_de0322f741f7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:46.650704+00:00
-- url     : https://prove2.me/submissions/0ff1d056-5b61-4147-b17b-d5f5a698e7b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]
omit [IsIntegral X]
namespace GroundTheory.Heights₂.Heights.Model.HeightOneSections
theorem _root_.solution {V : X.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(X, V)) :
    hV.fromSpec p ∈ V := by
  have h : hV.fromSpec p ∈ Set.range hV.fromSpec := ⟨p, rfl⟩
  rwa [hV.range_fromSpec] at h
end GroundTheory.Heights₂.Heights.Model.HeightOneSections

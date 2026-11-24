-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:47.952816+00:00
-- url     : https://prove2.me/submissions/5b1b72c6-56a9-4215-a929-c2c077470bca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
universe u
variable {X Y : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ≤ U) (x : Γ(M, U)) :
    (φ.app V).hom ((M.presheaf.map (homOfLE i).op).hom x) =
      (N.presheaf.map (homOfLE i).op).hom ((φ.app U).hom x) := by
  have := congr(($(φ.mapPresheaf.naturality (homOfLE i).op)).hom x)
  simpa using this
end GroundTheory.Heights₂.Heights.Model

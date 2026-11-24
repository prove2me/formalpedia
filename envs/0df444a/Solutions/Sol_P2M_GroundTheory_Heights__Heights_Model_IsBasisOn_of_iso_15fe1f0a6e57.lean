-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:21.362023+00:00
-- url     : https://prove2.me/submissions/b7ba76fe-d9bf-4353-9df6-4db7060b2e98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a

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
namespace IsBasisOn
theorem _root_.solution {M N : X.Modules} (e : M ≅ N) {U : X.Opens} {n : ℕ}
    {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    IsBasisOn N U (fun i => (e.hom.app U).hom (s i)) := by
  intro V h
  have key : (fun r : Fin n → Γ(X, V) =>
      ∑ i, r i • (N.presheaf.map (homOfLE h).op).hom ((e.hom.app U).hom (s i))) =
      (e.hom.app V).hom ∘ (fun r => ∑ i, r i • (M.presheaf.map (homOfLE h).op).hom (s i)) := by
    funext r
    simp only [Function.comp_apply, map_sum, Scheme.Modules.Hom.app_smul, app_map_apply]
  rw [key]
  have : IsIso (e.hom.app V) := inferInstance
  exact (ConcreteCategory.bijective_of_isIso (e.hom.app V)).comp (hs V h)
end IsBasisOn
end GroundTheory.Heights₂.Heights.Model

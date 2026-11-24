-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_comb_8d6e321d74e3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:47.034946+00:00
-- url     : https://prove2.me/submissions/868ab1a4-129b-4ab6-b079-9cc60880f8b6

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
theorem _root_.solution (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens)
    (h : W ≤ V) (r : Fin n → Γ(X, W)) (x : X) (hx : x ∈ W) :
    E.presheaf.germ W x hx (comb E s W h r) =
      ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x (h hx) (s i) := by
  rw [comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul']
  congr 1
  exact TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE h) x hx (s i)
end GroundTheory.Heights₂.Heights.Model.HeightOneSections

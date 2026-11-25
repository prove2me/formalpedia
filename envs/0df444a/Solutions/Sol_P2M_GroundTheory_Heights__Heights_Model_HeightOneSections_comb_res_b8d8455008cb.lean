-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_comb_res_b8d8455008cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:59.796331+00:00
-- url     : https://prove2.me/submissions/3e4d2026-1342-451f-8c73-d3070cb51c49

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
theorem _root_.solution (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W W' : X.Opens)
    (h : W ≤ V) (h' : W' ≤ W) (r : Fin n → Γ(X, W)) :
    E.presheaf.map (homOfLE h').op (comb E s W h r) =
      comb E s W' (h'.trans h) (fun i => X.presheaf.map (homOfLE h').op (r i)) := by
  rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.map_smul]
  congr 1
  show (E.presheaf.map (homOfLE h).op ≫ E.presheaf.map (homOfLE h').op) (s i) = _
  rw [← Functor.map_comp]
  rfl
end GroundTheory.Heights₂.Heights.Model.HeightOneSections

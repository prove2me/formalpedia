-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_res_res_ee0c529cdd77
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:54.009815+00:00
-- url     : https://prove2.me/submissions/f0c03763-bc40-4c87-af22-3619b4d420f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators

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
variable {X : Scheme.{0}} (M : X.Modules)
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C) (x : Γ(M, C)) :
    (M.presheaf.map i.op).hom ((M.presheaf.map j.op).hom x) = (M.presheaf.map k.op).hom x := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, CategoryTheory.Functor.map_comp]
  rfl
end GroundTheory.Heights₂.Heights.Model

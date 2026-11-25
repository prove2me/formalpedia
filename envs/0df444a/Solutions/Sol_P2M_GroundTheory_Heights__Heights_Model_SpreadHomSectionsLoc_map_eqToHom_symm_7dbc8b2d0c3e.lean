-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_map_eqToHom_symm_7dbc8b2d0c3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:08.664954+00:00
-- url     : https://prove2.me/submissions/54d2a4b8-aa59-4f09-9ad9-750919e06ba7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc

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
open GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
namespace GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
theorem _root_.solution (Z : Scheme.{0}) {A B : Z.Opens} (h : A = B) (x : Γ(Z, A)) :
    (Z.presheaf.map (eqToHom h).op).hom ((Z.presheaf.map (eqToHom h.symm).op).hom x) = x := by
  subst h
  simp
end GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc

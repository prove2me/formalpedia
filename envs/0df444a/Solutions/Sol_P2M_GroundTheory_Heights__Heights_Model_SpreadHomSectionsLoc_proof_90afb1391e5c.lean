-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_proof_90afb1391e5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:01.239184+00:00
-- url     : https://prove2.me/submissions/6a730026-1814-4cee-b172-c00e715e99db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_app_restrict_eq_nsmul_d1c116bc0518
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_main_de3e7704d2b0

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
namespace GroundTheory.Heights₂.Heights.Model
namespace SpreadHomSectionsLoc
theorem _root_.solution (h₁ : ZLocDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    (h₃ : PullInjLoc.Statement) : SpreadHomSectionsLoc.Statement := by
  intro X f _ _ p U F G hF hG φ
  obtain ⟨m₀, hm₀, hpm₀, hinj⟩ := h₃ X f p U G hG
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  have : CompactSpace (U : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (U : Set X))
  exact SpreadHomSectionsLoc.main _ _ p.2 h₂ (U.ι ≫ f)
    (fun W hW b => SpreadHomSectionsLoc.exists_app_restrict_eq_nsmul h₁ f p U W hW b) hF hG φ hm₀ hpm₀ hinj
end SpreadHomSectionsLoc
end GroundTheory.Heights₂.Heights.Model

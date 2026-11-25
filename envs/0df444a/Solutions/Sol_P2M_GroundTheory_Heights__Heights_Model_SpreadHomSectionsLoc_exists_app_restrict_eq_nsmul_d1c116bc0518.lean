-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_app_restrict_eq_nsmul_d1c116bc0518
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:58.173717+00:00
-- url     : https://prove2.me/submissions/e56cd7b6-2f5c-454d-9432-29a4f046cce3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_map_eqToHom_symm_7dbc8b2d0c3e

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
theorem _root_.solution (h₁ : ZLocDenominators.Statement) {X : Scheme.{0}}
    (f : X ⟶ SpecZ) (p : Nat.Primes) (U : X.Opens) (V : (U : Scheme.{0}).Opens) (hV : IsAffineOpen V)
    (b : Γ((baseChangeMap f (ZLoc p) ⁻¹ᵁ U : Scheme.{0}), (baseChangeMap f (ZLoc p) ∣_ U) ⁻¹ᵁ V)) :
    ∃ N : ℕ, 0 < N ∧ ¬ (p : ℕ) ∣ N ∧ ∃ c : Γ((U : Scheme.{0}), V),
      (baseChangeMap f (ZLoc p) ∣_ U).app V c = N • b := by
  have e := image_morphismRestrict_preimage (baseChangeMap f (ZLoc p)) U V
  obtain ⟨N, hN, hpN, c, hc⟩ := h₁ X f p (U.ι ''ᵁ V) (hV.image_of_isOpenImmersion U.ι)
    (((baseChange f (ZLoc p)).presheaf.map (eqToHom e.symm).op).hom b)
  refine ⟨N, hN, hpN, c, ?_⟩
  rw [morphismRestrict_app]
  change ((baseChange f (ZLoc p)).presheaf.map (eqToHom e).op).hom
    ((baseChangeMap f (ZLoc p)).app _ c) = N • b
  rw [hc, map_nsmul]
  congr 1
  exact map_eqToHom_symm _ e b
end GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc

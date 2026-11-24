-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_transMap_app_9788faf886f2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:49.570411+00:00
-- url     : https://prove2.me/submissions/d991298e-1bb2-45ac-a433-a46a34495236

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_unit_app_52e1385b04f1

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
open GroundTheory.Heights₂.Heights.Model.GlueModulesStar
universe u
set_option backward.isDefEq.respectTransparency false
open Scheme.Modules
namespace GroundTheory.Heights₂.Heights.Model.GlueModulesStar
theorem _root_.solution {A B Z : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f] (h : B ⟶ Z)
    {k : A ⟶ Z} (e : f ≫ h = k) {M : B.Modules} {N : A.Modules} (χ : (Scheme.Modules.pullback f).obj M ⟶ N)
    [IsIso χ] (O : Z.Opens) (hO : h ⁻¹ᵁ O ≤ f.opensRange) :
    IsIso ((transMap f h e χ).app O) := by
  simp only [transMap, Hom.comp_app, pushforward_map_app, Adjunction.homEquiv_unit,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app]
  have := isIso_unit_app f M (h ⁻¹ᵁ O) hO
  exact IsIso.comp_isIso' (IsIso.comp_isIso' this inferInstance)
    (IsIso.comp_isIso' (IsIso.id _) inferInstance)
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar

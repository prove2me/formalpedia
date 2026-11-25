-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:48.107954+00:00
-- url     : https://prove2.me/submissions/97b43c43-99bd-49f8-b8d3-21950c87725c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp_be5f85a3764b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackComp_trans_congr_76dd066c1c0a

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
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k') (e' : g' ≫ h = k')
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e' γ = pullbackCompIso ek (Iso.refl _) ≪≫
      (Scheme.Modules.pullback t).mapIso (pullbackCompIso e γ) ≪≫
      (pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F))).symm := by
  rw [pullbackCompIso_comp t e eg ek e' γ, pullbackComp_trans_congr,
    pullbackCompIso_eq_refl_trans ek (pullbackCompIso e γ), Iso.trans_assoc]
end GroundTheory.Heights₂.Heights.Model

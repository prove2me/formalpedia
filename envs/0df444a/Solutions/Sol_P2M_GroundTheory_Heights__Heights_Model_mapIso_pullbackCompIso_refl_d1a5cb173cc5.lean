-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackCompIso_refl_d1a5cb173cc5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:58.286664+00:00
-- url     : https://prove2.me/submissions/770af9fd-0ef7-4ebf-baa5-bab122952931

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d

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
theorem _root_.solution (t : T' ⟶ T) {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) {g' : T' ⟶ Y} (eg : t ≫ g = g') {k' : T' ⟶ Z} (ek : t ≫ k = k')
    (e' : g' ≫ h = k') (E : Z.Modules) :
    (Scheme.Modules.pullback t).mapIso (pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback h).obj E))) =
      (pullbackCompIso ek (Iso.refl _)).symm ≪≫ pullbackCompIso e' (Iso.refl _) ≪≫
        pullbackCompIso eg (Iso.refl _) := by
  rw [pullbackCompIso_comp' t e eg ek e']
  ext1
  simp
end GroundTheory.Heights₂.Heights.Model

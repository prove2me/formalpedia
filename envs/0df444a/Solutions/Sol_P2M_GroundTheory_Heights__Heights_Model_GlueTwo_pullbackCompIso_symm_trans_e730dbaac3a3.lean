-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueTwo_pullbackCompIso_symm_trans_e730dbaac3a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:30.587261+00:00
-- url     : https://prove2.me/submissions/0061eb9d-3adc-435a-8603-c46285789856

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueTwo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_comp__3ff0e312897d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543


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
open GroundTheory.Heights₂.Heights.Model.GlueTwo
namespace GroundTheory.Heights₂.Heights.Model.GlueTwo
theorem _root_.solution {A B C Z : Scheme.{0}} {t : A ⟶ B} {s : B ⟶ C} {ι : C ⟶ Z}
    {j : B ⟶ Z} {u : A ⟶ C} {w : A ⟶ Z} (e : s ≫ ι = j) (eg : t ≫ s = u) (ek : t ≫ j = w)
    (e' : u ≫ ι = w) {E : Z.Modules} {F : B.Modules} (a : (Scheme.Modules.pullback j).obj E ≅ F) :
    pullbackCompIso eg ((pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫ a) =
      (pullbackCompIso e' (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫
        pullbackCompIso ek a := by
  rw [pullbackCompIso_comp' t e eg ek e' (Iso.refl ((Scheme.Modules.pullback ι).obj E)),
    pullbackCompIso_eq_refl_trans eg
      ((pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback ι).obj E))).symm ≪≫ a),
    pullbackCompIso_eq_refl_trans ek a, Functor.mapIso_trans, Functor.mapIso_symm]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]
end GroundTheory.Heights₂.Heights.Model.GlueTwo

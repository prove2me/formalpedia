-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_refl_naturality_981471ea787c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:06:18.286296+00:00
-- url     : https://prove2.me/submissions/74700953-db44-4947-a221-d3663c925f25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
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
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (t : T' ⟶ T) {g : T ⟶ Y} {g' : T' ⟶ Y} (eg : t ≫ g = g')
    {F F' : Y.Modules} (δ : F ≅ F') :
    pullbackCompIso eg (Iso.refl ((Scheme.Modules.pullback g).obj F)) ≪≫
        (Scheme.Modules.pullback t).mapIso ((Scheme.Modules.pullback g).mapIso δ) =
      (Scheme.Modules.pullback g').mapIso δ ≪≫ pullbackCompIso eg (Iso.refl _) := by
  rw [← pullbackCompIso_eq_refl_trans]
  subst eg
  ext1
  have nat := (Scheme.Modules.pullbackComp t g).inv.naturality δ.hom
  simp only [Functor.comp_map] at nat
  simp [pullbackCompIso, Scheme.Modules.pullbackCongr, nat]
end GroundTheory.Heights₂.Heights.Model

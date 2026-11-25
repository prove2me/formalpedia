-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackIsoAlong_3c729adf96c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:28.271299+00:00
-- url     : https://prove2.me/submissions/bbec22db-3d49-4246-a8f6-4a8500e815d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mapIso_pullbackCompIso_refl_d1a5cb173cc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_refl_naturality_981471ea787c

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
theorem _root_.solution {W' W O O' : Scheme.{0}} (u : W' ⟶ W) {t : W ⟶ O'} {h : O' ⟶ O}
    {k : W ⟶ O} (ek : t ≫ h = k) {t' : W' ⟶ O'} {k' : W' ⟶ O} (ee : t' ≫ h = k')
    (ut : u ≫ t = t') (uk : u ≫ k = k') {A B : O.Modules}
    (ψ : (Scheme.Modules.pullback h).obj A ≅ (Scheme.Modules.pullback h).obj B) :
    (Scheme.Modules.pullback u).mapIso (pullbackIsoAlong ek ψ) =
      (pullbackCompIso uk (Iso.refl ((Scheme.Modules.pullback k).obj A))).symm ≪≫
        pullbackIsoAlong ee ψ ≪≫ pullbackCompIso uk (Iso.refl _) := by
  have hA := mapIso_pullbackCompIso_refl u ek ut uk ee A
  have hB := mapIso_pullbackCompIso_refl u ek ut uk ee B
  have nat := pullbackCompIso_refl_naturality u ut ψ
  simp only [pullbackIsoAlong, Functor.mapIso_trans, Functor.mapIso_symm, hA, hB]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  congr 2
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, nat]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
end GroundTheory.Heights₂.Heights.Model

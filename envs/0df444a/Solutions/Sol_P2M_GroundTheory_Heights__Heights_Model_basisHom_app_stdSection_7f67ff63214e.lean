-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_basisHom_app_stdSection_7f67ff63214e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:11.456442+00:00
-- url     : https://prove2.me/submissions/90b71e68-ac4e-42d3-a5d8-03cd60212efc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBasisIsoFree

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
universe u
variable {Y : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤)) (i : Fin n) :
    ((basisHom M s).app ⊤).hom (stdSection Y n i) = s i := by
  have h1 : SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i) ≫ basisHom M s =
      M.unitHomEquiv.symm (globalSectionFamily M (s i)) := by
    refine (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (basisHom M s) (ULift.up i)).symm.trans ?_
    congr 1
    exact congrFun ((SheafOfModules.freeHomEquiv M).apply_symm_apply _) (ULift.up i)
  have e1 : (M.unitHomEquiv (SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i) ≫
      basisHom M s)).val (op ⊤) = (globalSectionFamily M (s i)).val (op ⊤) := by
    have := congrArg (fun φ => (M.unitHomEquiv φ).val (op ⊤)) h1
    simpa only [Equiv.apply_symm_apply] using this
  have e2 : (M.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op).hom (s i) = s i := by
    rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
    simp
  exact e1.trans (by exact e2)
end GroundTheory.Heights₂.Heights.Model

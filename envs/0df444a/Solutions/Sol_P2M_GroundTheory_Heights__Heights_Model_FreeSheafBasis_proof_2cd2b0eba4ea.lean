-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_proof_2cd2b0eba4ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:13.354069+00:00
-- url     : https://prove2.me/submissions/e27b32cb-5eda-4304-8944-05b0ff0eb9f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_app_0d695d7a260d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_incl_proj_app_bbd2a82a7041
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a


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
open FreeSheafBasis
namespace GroundTheory.Heights₂.Heights.Model
namespace FreeSheafBasis
theorem _root_.solution : FreeSheafBasis.Statement.{u} := by
  intro Y n V h
  have h1 : ((structureModule Y).presheaf.map (homOfLE h).op).hom (1 : Γ(Y, ⊤)) = (1 : Γ(Y, V)) := by
    change (Y.presheaf.map (homOfLE h).op).hom 1 = 1
    exact map_one _
  have hres : ∀ i (r : Γ(Y, V)), r • ((freeModule Y n).presheaf.map (homOfLE h).op).hom
      (stdSection Y n i) = ((incl Y n i).app V).hom r := by
    intro i r
    have e := app_map_apply (incl Y n i) h (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤)))
    have h1' : ((structureModule Y).presheaf.map (homOfLE h).op).hom
        (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤))) =
        (show Γ(structureModule Y, V) from (1 : Γ(Y, V))) := h1
    rw [h1'] at e
    have e2 := Scheme.Modules.Hom.app_smul (incl Y n i) r
      (show Γ(structureModule Y, V) from (1 : Γ(Y, V)))
    have hr : r • (show Γ(structureModule Y, V) from (1 : Γ(Y, V))) =
        (show Γ(structureModule Y, V) from r) := mul_one r
    change r • ((freeModule Y n).presheaf.map (homOfLE h).op).hom
      (((incl Y n i).app ⊤).hom (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤)))) = _
    rw [← e]
    exact e2.symm.trans (congrArg (fun x => (incl Y n i).app V x) hr)
  simp only [hres]
  refine Function.bijective_iff_has_inverse.mpr ⟨fun m j => ((proj Y n j).app V).hom m, ?_, ?_⟩
  · intro r
    funext j
    simp only [map_sum, incl_proj_app]
    change (∑ x, if x = j then r x else 0 : Γ(Y, V)) = r j
    simp
  · intro m
    exact sum_incl_proj_app V m
end FreeSheafBasis
end GroundTheory.Heights₂.Heights.Model

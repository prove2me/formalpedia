-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_incl_proj_app_bbd2a82a7041
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:23.264294+00:00
-- url     : https://prove2.me/submissions/6276be46-ae7c-4400-856e-d8435e430163

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_proj_incl_59ea9a70b16f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_evalHom_apply_01d7b863b51a

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
open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
variable (Y : Scheme.{u}) (n : ℕ)
variable {Y n}
namespace GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
theorem _root_.solution (V : Y.Opens) (m : Γ(freeModule Y n, V)) :
    ∑ j, ((incl Y n j).app V).hom (((proj Y n j).app V).hom m) = m := by
  have := congrArg (fun φ => evalHom V m φ) (sum_proj_incl Y n)
  simp only [map_sum, evalHom_apply] at this
  exact this
end GroundTheory.Heights₂.Heights.Model.FreeSheafBasis

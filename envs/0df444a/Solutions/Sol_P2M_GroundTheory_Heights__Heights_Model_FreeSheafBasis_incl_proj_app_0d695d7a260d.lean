-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_app_0d695d7a260d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:51.161816+00:00
-- url     : https://prove2.me/submissions/4d34b970-8308-46c7-8e63-ea6997f3b37e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_2dae232b015b

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
theorem _root_.solution (V : Y.Opens) (i j : Fin n) (r : Γ(Y, V)) :
    ((proj Y n j).app V).hom (((incl Y n i).app V).hom r) = if i = j then r else 0 := by
  have := congrArg (fun φ => evalHom (M := structureModule Y) (N := structureModule Y) V
    (show Γ(structureModule Y, V) from r) φ) (incl_proj Y n i j)
  split_ifs at this ⊢ with hij <;> exact this
end GroundTheory.Heights₂.Heights.Model.FreeSheafBasis

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_tensor_tensor_comm_cc0e4bf9cb6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:57:35.419559+00:00
-- url     : https://prove2.me/submissions/44279556-295d-4927-830f-4328b8c86eee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hermLine_ext_b7bdcdc64384

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution (A B C D : HermLine ι) :
    (A.tensor B).tensor (C.tensor D) = (A.tensor C).tensor (B.tensor D) :=
  hermLine_ext (add_add_add_comm _ _ _ _) (funext fun _ => mul_mul_mul_comm _ _ _ _)
end GroundTheory.Heights₂.Heights.Inter.ThmIExists

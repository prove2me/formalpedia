-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:39.456274+00:00
-- url     : https://prove2.me/submissions/c2371297-3ebd-4f84-a552-6ab175dd933c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt.mulBy_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
theorem _root_.solution (B : Subring L) (H : AddSubgroup B) :
    (H.map B.subtype.toAddMonoidHom).relIndex B.toAddSubgroup = H.index := by
  have hinj : Function.Injective B.subtype.toAddMonoidHom := Subtype.val_injective
  have hr : (⊤ : AddSubgroup B).map B.subtype.toAddMonoidHom = B.toAddSubgroup := by
    ext x
    simp
  rw [← hr, ← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hinj,
    AddSubgroup.relIndex_top_right]
end GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt

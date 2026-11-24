-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_ba0dcb3ccb8a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:43.415319+00:00
-- url     : https://prove2.me/submissions/6011cbdc-be8a-48ed-814b-15b39c9fbceb

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
theorem _root_.solution (B : Subring L) (β : B) :
    B.toAddSubgroup.map (mulBy (β : L)) =
      (Ideal.span {β}).toAddSubgroup.map B.subtype.toAddMonoidHom := by
  ext x
  simp only [AddSubgroup.mem_map, mulBy_apply, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩ * β, ⟨⟨y, hy⟩, rfl⟩, by simp [mul_comm]⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, c.2, by simp [mul_comm]⟩
end GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt

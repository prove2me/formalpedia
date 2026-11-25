-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_card_one_eq_zero_894d9c562d28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:18.453819+00:00
-- url     : https://prove2.me/submissions/03c78409-850d-418e-a6ce-fcb92e89f10c

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
theorem _root_.solution [NumberField L] : Nat.card (1 : Submodule (𝓞 L) L).toAddSubgroup = 0 := by
  have : Infinite (1 : Submodule (𝓞 L) L).toAddSubgroup :=
    Infinite.of_injective (fun n : ℕ => (⟨(n : L), Submodule.mem_one.mpr ⟨n, by simp⟩⟩ :
      (1 : Submodule (𝓞 L) L).toAddSubgroup))
      (fun m n h => Nat.cast_injective (R := L) (congrArg Subtype.val h))
  exact Nat.card_eq_zero_of_infinite
end GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt

-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_one_of_mem_62c5ae2e4464
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:44.8687+00:00
-- url     : https://prove2.me/submissions/b475cd69-d643-4fe2-9799-ba066e0d67e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
theorem _root_.solution [NumberField L] {B : Subring L} [Module.Finite ℤ B] {b : L} (hb : b ∈ B) :
    b ∈ (1 : Submodule (𝓞 L) L) := by
  have h := mul_mem_of_mem (S := 1) hb (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  rwa [mul_one] at h
end GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt

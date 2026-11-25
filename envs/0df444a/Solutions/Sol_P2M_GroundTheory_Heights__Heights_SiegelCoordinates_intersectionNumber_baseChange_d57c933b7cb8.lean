-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SiegelCoordinates_intersectionNumber_baseChange_d57c933b7cb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:22.875076+00:00
-- url     : https://prove2.me/submissions/5c556bf9-6fd8-441e-8b13-105788e0da89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordSiegel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_siegelGram_mem_posDef_2f7eb0d9c3c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KCoord_existsUnique_siegelGram_9ab454a621dd

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
open Matrix
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace SiegelCoordinates
theorem _root_.solution : SiegelCoordinates.Statement := fun _ =>
  ⟨fun X Y hX hY => KCoord.siegelGram_mem_posDef X Y hX hY,
    fun G hS hG => KCoord.existsUnique_siegelGram G hS hG⟩
end SiegelCoordinates
end GroundTheory.Heights₂.Heights

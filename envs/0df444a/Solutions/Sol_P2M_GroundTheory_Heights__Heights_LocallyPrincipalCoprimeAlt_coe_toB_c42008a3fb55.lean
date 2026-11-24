-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_coe_toB_c42008a3fb55
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:45.436819+00:00
-- url     : https://prove2.me/submissions/5b2713a8-4de9-4ae7-8568-efe90a403605

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime

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
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
theorem _root_.solution {B : Subring L} {x : L} (h : x ∈ B) : (toB B x : L) = x := by
  simp [toB, h]
end GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt

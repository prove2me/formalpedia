-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SupportCycleSection_proof_f753980cb5af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:24.202223+00:00
-- url     : https://prove2.me/submissions/340ed52c-4750-4fd2-b98d-a3183a735160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSupportCycleSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_support_cycleSection_iff_139ed4531e1a

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
namespace GroundTheory.Heights₂.Heights
namespace SupportCycleSection
theorem _root_.solution : SupportCycleSection.Statement := by
  intro n Z u
  refine ⟨fun W hW W' hW' => (mem_support_cycleSection_iff Z u W').mpr ⟨W, hW, hW'⟩,
    fun W' hW' => (mem_support_cycleSection_iff Z u W').mp hW'⟩
end SupportCycleSection
end GroundTheory.Heights₂.Heights

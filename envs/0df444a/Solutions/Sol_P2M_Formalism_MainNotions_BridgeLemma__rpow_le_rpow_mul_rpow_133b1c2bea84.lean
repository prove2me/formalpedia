-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rpow_le_rpow_mul_rpow_133b1c2bea84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:56.260125+00:00
-- url     : https://prove2.me/submissions/848b27b5-692b-4def-85ce-8c0a98010b0d

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsOneN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {P σ h c : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4) (hc : 0 ≤ c) :
    h ^ c ≤ P ^ c * σ ^ (4 * c) := by
  have h0 : 0 ≤ h := by linarith
  have hσ0 : 0 ≤ σ := by linarith
  calc h ^ c ≤ (P * σ ^ 4) ^ c := Real.rpow_le_rpow h0 hh hc
    _ = P ^ c * (σ ^ 4) ^ c := Real.mul_rpow (by linarith) (by positivity)
    _ = P ^ c * σ ^ (4 * c) := by
      rw [← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ0] <;> norm_num
end Formalism.MainNotions.BridgeLemma₂

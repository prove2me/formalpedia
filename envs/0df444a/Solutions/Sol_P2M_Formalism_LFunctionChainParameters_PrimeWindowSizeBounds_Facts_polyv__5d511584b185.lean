-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyv__5d511584b185
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:47.93591+00:00
-- url     : https://prove2.me/submissions/0f662042-0769-4628-8881-90c52d46e391

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Epos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_br_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_mono3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
theorem _root_.solution {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * v ≤ sg P K * P.b := by
  refine le_trans ?_ F.br_sg
  have h1 := F.mono3 hi hj
  have h2 := F.Kpos
  have h4 : 0 ≤ E ^ i * P.x ^ j := mul_nonneg (pow_nonneg F.Epos.le _) (pow_nonneg F.xpos.le _)
  have h5 := F.v0
  calc c * K * (E ^ i * P.x ^ j) * v ≤ 100 * K * (E ^ 4 * P.x ^ 4 * P.x⁻¹) * v := by gcongr
    _ = (100 * K * (E ^ 4 * P.x ^ 4)) * v * P.x⁻¹ := by ring
    _ ≤ X * v * P.x⁻¹ := by
        have := F.hXB
        have := F.rpos
        gcongr
    _ = P.b * P.x⁻¹ := by rw [mul_comm X v, F.hvX]
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts

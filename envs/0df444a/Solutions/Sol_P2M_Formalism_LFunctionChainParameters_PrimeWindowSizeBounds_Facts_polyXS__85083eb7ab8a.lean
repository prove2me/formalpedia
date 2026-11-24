-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyXS__85083eb7ab8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:11.830924+00:00
-- url     : https://prove2.me/submissions/314d1a3f-61ba-45c7-bf9b-4eb428a9807f

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Epos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_one_le_x_mul_s
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hbXS
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
    c * K * (E ^ i * P.x ^ j) * (X * S) ≤ sg P K * P.b := by
  refine le_trans ?_ F.br_sg
  have h1 := F.mono3 hi hj
  have h2 := F.Kpos
  have h3 := F.one_le_x_mul_s
  have h4 : 0 ≤ E ^ i * P.x ^ j := mul_nonneg (pow_nonneg F.Epos.le _) (pow_nonneg F.xpos.le _)
  calc c * K * (E ^ i * P.x ^ j) * (X * S) ≤ 100 * K * (E ^ 4 * P.x ^ 4 * P.x⁻¹) * (X * S) := by gcongr
    _ = (100 * K * (E ^ 4 * P.x ^ 4) * (X * S)) * P.x⁻¹ := by ring
    _ ≤ P.b * P.x⁻¹ := mul_le_mul_of_nonneg_right F.hbXS F.rpos.le
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts

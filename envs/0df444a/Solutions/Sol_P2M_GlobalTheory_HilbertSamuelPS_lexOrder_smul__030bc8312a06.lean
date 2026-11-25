-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_smul__030bc8312a06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:30.822468+00:00
-- url     : https://prove2.me/submissions/e58ac29c-1858-4f5e-a549-07ad9f3439e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_congr__ff567c48da14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D : ℕ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution {c : ℂ} (hc : c ≠ 0) (g : MvPowerSeries (Fin D) ℂ) :
    lexOrder (c • g) = lexOrder g :=
  lexOrder_congr' fun d => by simp [hc]
end GlobalTheory.HilbertSamuelPS

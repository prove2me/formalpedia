-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_congr__ff567c48da14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:31.428881+00:00
-- url     : https://prove2.me/submissions/3c744581-df2d-4c13-ae80-289ebf0da8f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

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
theorem _root_.solution {g h : MvPowerSeries (Fin D) ℂ}
    (H : ∀ d, coeff d g = 0 ↔ coeff d h = 0) : lexOrder g = lexOrder h :=
  le_antisymm (le_lexOrder_iff.mpr fun d hd => (H d).1 (coeff_eq_zero_of_lt_lexOrder hd))
    (le_lexOrder_iff.mpr fun d hd => (H d).2 (coeff_eq_zero_of_lt_lexOrder hd))
end GlobalTheory.HilbertSamuelPS

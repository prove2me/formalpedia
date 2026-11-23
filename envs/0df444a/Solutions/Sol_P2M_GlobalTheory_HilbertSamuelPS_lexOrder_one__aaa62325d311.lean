-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_one__aaa62325d311
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:47.548288+00:00
-- url     : https://prove2.me/submissions/e9d6f70b-2fca-487d-aa17-493e8accfe93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_monomial_one__d29802e760af

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
theorem _root_.solution :
    lexOrder (1 : MvPowerSeries (Fin D) ℂ) = ((toLex (0 : Fin D →₀ ℕ) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  rw [← lexOrder_monomial_one' 0]; simp
end GlobalTheory.HilbertSamuelPS

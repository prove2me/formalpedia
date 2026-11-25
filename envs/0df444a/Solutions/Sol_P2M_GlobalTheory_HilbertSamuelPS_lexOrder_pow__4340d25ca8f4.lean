-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_pow__4340d25ca8f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:35.154407+00:00
-- url     : https://prove2.me/submissions/0d4b75f0-aaf0-4dcd-a022-41d96e30ab45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_one__aaa62325d311

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
theorem _root_.solution {g : MvPowerSeries (Fin D) ℂ} {e : Fin D →₀ ℕ}
    (he : lexOrder g = ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ)))) (k : ℕ) :
    lexOrder (g ^ k) = ((toLex (k • e) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  induction k with
  | zero => simpa using lexOrder_one' (D := D)
  | succ k ih => rw [pow_succ, lexOrder_mul, ih, he, succ_nsmul, ← WithTop.coe_add, ← toLex_add]
end GlobalTheory.HilbertSamuelPS

-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_prod_X_pow__790a47b3fadf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:37.943144+00:00
-- url     : https://prove2.me/submissions/e9582041-b89f-4d04-96f2-3a54f95e5c2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_monomial_one__d29802e760af
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
theorem _root_.solution (a : Fin D → ℕ) :
    lexOrder (∏ i, (X i : MvPowerSeries (Fin D) ℂ) ^ a i) =
      ((toLex (∑ i, Finsupp.single i (a i)) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  classical
  suffices ∀ s : Finset (Fin D), lexOrder (∏ i ∈ s, (X i : MvPowerSeries (Fin D) ℂ) ^ a i) =
      ((toLex (∑ i ∈ s, Finsupp.single i (a i)) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) from this _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using lexOrder_one' (D := D)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, lexOrder_mul, ih, X_pow_eq,
      lexOrder_monomial_one', ← WithTop.coe_add, ← toLex_add]
end GlobalTheory.HilbertSamuelPS

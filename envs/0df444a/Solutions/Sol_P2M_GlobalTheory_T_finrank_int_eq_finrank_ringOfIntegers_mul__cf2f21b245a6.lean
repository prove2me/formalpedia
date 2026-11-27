-- Prove2me | solution 1 for P2M_GlobalTheory_T_finrank_int_eq_finrank_ringOfIntegers_mul__cf2f21b245a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:03.148206+00:00
-- url     : https://prove2.me/submissions/ae92b4e9-a9fe-440a-99e7-a0327e451b34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankIntEqFinrankRingOfIntegersMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankIntEqFinrankRingOfIntegersMulStatement
import Theorems.Thm_GlobalTheory_finrank_int_eq_finrank_ringOfIntegers_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N], Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E := by
  first | exact @GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul | exact GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul | (intros; apply GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul <;> assumption)
end _root_.GlobalTheory.T

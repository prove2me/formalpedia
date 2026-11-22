-- Prove2me | solution 1 for UpperTheory.MUQ.int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:37.295298+00:00
-- url     : https://prove2.me/submissions/13c04ae4-a3cf-4d14-ba0b-0567b8003181

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory
variable {E K K' : Type} [Field E] [Field K] [Field K'] {ι ι' : Type} [Fintype ι] [Fintype ι']
open UpperTheory.MUQ
variable {φ : ι → E →+* K} {e : ι → ℚ}
namespace UpperTheory.MUQ
theorem _root_.solution (h : MUQ φ e) (i : ι) : ∃ z : ℤ, e i = z := let ⟨a, ha, _⟩ := h; ⟨a i, ha i⟩
end UpperTheory.MUQ

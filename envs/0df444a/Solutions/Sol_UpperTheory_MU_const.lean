-- Prove2me | solution 1 for UpperTheory.MU.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:57.613711+00:00
-- url     : https://prove2.me/submissions/7bdc1f55-5fed-40af-9df2-98c14da516b4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_UpperTheory_MU_smul

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
open UpperTheory.MU
variable {φ : ι → E →+* K} {e e' : ι → ℤ}
namespace UpperTheory.MU
theorem _root_.solution (h : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun _ => c) := by
  have h2 := h.smul c
  simpa using h2
end UpperTheory.MU

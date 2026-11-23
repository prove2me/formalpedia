-- Prove2me | solution 1 for UpperTheory.MU.add_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:49.057721+00:00
-- url     : https://prove2.me/submissions/37964f8d-c69d-439b-a1f5-8de820eee448

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_UpperTheory_MU_add
import Theorems.Thm_UpperTheory_MU_const

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
theorem _root_.solution (h : MU φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun i => e i + c) :=
  h.add (h1.const c)
end UpperTheory.MU

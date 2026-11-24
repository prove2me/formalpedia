-- Prove2me | solution 1 for UpperTheory.MU.equiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:01.051854+00:00
-- url     : https://prove2.me/submissions/25211d47-8b67-4217-86de-14987d427ed9

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
open UpperTheory.MU
variable {φ : ι → E →+* K} {e e' : ι → ℤ}
namespace UpperTheory.MU
theorem _root_.solution (s : ι' ≃ ι) : MU (fun i => φ (s i)) (fun i => e (s i)) ↔ MU φ e := by
  refine forall_congr' fun z => forall_congr' fun _ => ?_
  rw [Equiv.prod_comp s (fun i => φ i z ^ e i)]
end UpperTheory.MU

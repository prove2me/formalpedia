-- Prove2me | solution 1 for UpperTheory.MUQ.equiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:08.469707+00:00
-- url     : https://prove2.me/submissions/d086025f-a0d7-4a10-b46c-c2992a1859fc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_UpperTheory_MU_equiv_iff

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
theorem _root_.solution (s : ι' ≃ ι) : MUQ (fun i => φ (s i)) (fun i => e (s i)) ↔ MUQ φ e := by
  constructor
  · rintro ⟨a, ha, hm⟩
    refine ⟨fun i => a (s.symm i), fun i => by simpa using ha (s.symm i), ?_⟩
    rw [← MU.equiv_iff s]
    simpa using hm
  · rintro ⟨a, ha, hm⟩
    exact ⟨fun i => a (s i), fun i => ha _, (MU.equiv_iff s).2 hm⟩
end UpperTheory.MUQ

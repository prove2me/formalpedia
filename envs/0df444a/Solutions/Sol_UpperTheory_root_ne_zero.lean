-- Prove2me | solution 1 for UpperTheory.root_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:23.245414+00:00
-- url     : https://prove2.me/submissions/299efbbd-2245-455a-8294-453550920666

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
namespace UpperTheory
theorem _root_.solution {z : E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : z ≠ 0 := by
  obtain ⟨m, hm, h⟩ := hz
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h
end UpperTheory

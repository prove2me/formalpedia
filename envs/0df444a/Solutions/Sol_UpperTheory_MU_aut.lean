-- Prove2me | solution 1 for UpperTheory.MU.aut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:53.947834+00:00
-- url     : https://prove2.me/submissions/a603c06f-3499-4584-9812-75fbe915f28b

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
theorem _root_.solution (h : MU φ e) (g : E →+* E) : MU (fun i => (φ i).comp g) e := fun z hz => by
  obtain ⟨m, hm, hzm⟩ := hz
  exact h (g z) ⟨m, hm, by rw [← map_pow, hzm, map_one]⟩
end UpperTheory.MU

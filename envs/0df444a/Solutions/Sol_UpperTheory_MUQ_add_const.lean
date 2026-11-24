-- Prove2me | solution 1 for UpperTheory.MUQ.add_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:04.58644+00:00
-- url     : https://prove2.me/submissions/a007939d-1f7b-4131-bfe6-cb968b46b006

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_UpperTheory_MU_add_const

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
theorem _root_.solution (h : MUQ φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MUQ φ (fun i => e i + c) := by
  obtain ⟨a, ha, hm⟩ := h
  exact ⟨fun i => a i + c, fun i => by simp [ha], hm.add_const h1 c⟩
end UpperTheory.MUQ

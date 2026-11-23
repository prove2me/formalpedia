-- Prove2me | solution 1 for UpperTheory.MUQ.mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:36.925382+00:00
-- url     : https://prove2.me/submissions/4708a18d-8a59-4afe-ba3f-3e31be086ed5

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
theorem _root_.solution (h : MUQ φ e) {a : ι → ℤ} (ha : ∀ i, e i = a i) : MU φ a := by
  obtain ⟨b, hb, hm⟩ := h
  have hab : a = b := funext fun i => by
    have h3 := (ha i).symm.trans (hb i)
    exact_mod_cast h3
  subst hab
  exact hm
end UpperTheory.MUQ

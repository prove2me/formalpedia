-- Prove2me | solution 1 for UpperTheory.MUQ.num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:13.966446+00:00
-- url     : https://prove2.me/submissions/c49df31a-5008-44e7-bfdb-d92334f6f25b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_IffNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.MUQ
variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {φ : ι → E →+* K} {e : ι → ℚ}
namespace UpperTheory.MUQ
theorem _root_.solution (h : MUQ φ e) : MU φ (fun i => (e i).num) := by
  obtain ⟨a, ha, hMU⟩ := h
  have : (fun i => (e i).num) = a := by
    funext i
    rw [ha i, Rat.num_intCast]
  rw [this]
  exact hMU
end UpperTheory.MUQ

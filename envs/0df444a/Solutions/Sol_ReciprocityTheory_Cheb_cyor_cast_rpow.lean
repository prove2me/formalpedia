-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyor_cast_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:55.111994+00:00
-- url     : https://prove2.me/submissions/6667224b-1a1f-4f70-8a7f-16f5acf722b3

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (q : Prm E) (s : ℝ) :
    ((((Nrm q : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) = ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp
end ReciprocityTheory.Cheb

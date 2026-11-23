-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_proj_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:47:51.8918+00:00
-- url     : https://prove2.me/submissions/fb14a995-31ec-4567-80e3-bcd5572aac9a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (x : Fin r → K) : projGe K r e x = 0 ↔ x ∈ cutSub K r e := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [projGe, hi] using this
  · intro h
    funext i
    by_cases hi : e ≤ (i : ℕ)
    · simp [projGe, hi, h i hi]
    · simp [projGe, hi]
end ReciprocityTheory.MultiplicativeHeights

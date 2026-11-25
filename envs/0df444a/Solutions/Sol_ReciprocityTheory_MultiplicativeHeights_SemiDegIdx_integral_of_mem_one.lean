-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.integral_of_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:43.541776+00:00
-- url     : https://prove2.me/submissions/8aecc332-1a2d-408a-924d-9cdc7bae64fb

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : IsIntegralElt x := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx
  exact ⟨a, ha⟩
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

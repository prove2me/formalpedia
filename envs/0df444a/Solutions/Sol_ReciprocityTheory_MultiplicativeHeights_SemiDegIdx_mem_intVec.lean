-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.mem_intVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:50.505462+00:00
-- url     : https://prove2.me/submissions/ffff3f5b-ac62-4903-bda5-05294fe05c5f

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA

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
open NumberField
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} {x : Fin k → K} :
    x ∈ intVec K k ↔ ∀ i, x i ∈ (1 : Submodule (𝓞 K) K) := by
  simp [intVec, Submodule.mem_pi]
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.vec_selfDual_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:13.518828+00:00
-- url     : https://prove2.me/submissions/4386e791-3cd9-4891-b5d2-898d7a6f0db6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_split_norm

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
open scoped nonZeroDivisors Pointwise
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (X : Submodule (𝓞 K) (Fin k → K)) (hfg : X.FG) (hstd : intVec K k ≤ X)
    (hsd : IsSelfDual S X) : |Algebra.norm ℚ S.G.det| ≤ (vecIdx X : ℚ) ^ 2 := by
  by_cases hG : S.G.det = 0
  · rw [hG, Algebra.norm_zero, abs_zero]
    positivity
  obtain ⟨J, hJ1, hJsd, hJ⟩ := split_norm S X hfg hstd hsd.1
  have hJe : J = 1 := le_antisymm hJ1 (hJsd hsd hG)
  rw [hJe, map_one, one_mul] at hJ
  exact hJ.ge
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

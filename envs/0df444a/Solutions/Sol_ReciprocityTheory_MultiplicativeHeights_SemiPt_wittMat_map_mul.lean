-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.wittMat_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:33:57.953354+00:00
-- url     : https://prove2.me/submissions/7b90e829-f33c-43fe-866b-4847fe622041

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_wPart
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wittMat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (σ : K →+* ℂ)
    (v : Fin r → ℂ) :
    (wittMat r m g).map σ * diagonal v * (wittMat r m g).map σ =
      diagonal fun i => σ (wVal r m g i) * v (wPart r m i) * σ (wVal r m g (wPart r m i)) := by
  rw [wittMat_eq]
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (wPart r m i)]
  · simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_pos rfl, wPart_wPart,
      Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [if_neg (Ne.symm hik), if_neg hik, map_zero, mul_zero]
  · intro j _ hj
    simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_neg hj, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end ReciprocityTheory.MultiplicativeHeights.SemiPt

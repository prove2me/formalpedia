-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.wittMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:14.897205+00:00
-- url     : https://prove2.me/submissions/2f174d09-baed-4a49-a17e-8749dce5f587

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_outer
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_mid
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wVal_outer
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wVal_mid

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
theorem _root_.solution {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) :
    wittMat r m g = Matrix.of fun i j => if j = wPart r m i then wVal r m g i else 0 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [wittMat, Matrix.of_apply]
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [wPart_outer r m i h, wVal_outer r m g i h]
    by_cases hj' : j = Fin.rev i
    · subst hj'
      rw [if_pos rfl, if_pos (by simp only [Fin.val_rev]; omega)]
    · rw [if_neg hj']
      rw [if_neg (by rintro ⟨h1, -⟩; apply hj'; ext; simp only [Fin.val_rev]; omega),
        if_neg (by rintro ⟨rfl, h2, h3⟩; omega)]
  · rw [wPart_mid r m i h, wVal_mid r m g i h]
    by_cases hij : j = i
    · subst hij
      rw [if_pos rfl, if_neg (by rintro ⟨h1, h2⟩; omega), if_pos ⟨rfl, by omega, by omega⟩]
    · rw [if_neg hij, if_neg (by rintro ⟨h1, h2⟩; omega), if_neg (by rintro ⟨h1, -⟩; exact hij h1.symm)]
end ReciprocityTheory.MultiplicativeHeights.SemiPt

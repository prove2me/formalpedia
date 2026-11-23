-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.formM_witt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:26.86014+00:00
-- url     : https://prove2.me/submissions/45e165bf-ca0e-4777-ab72-aaddedbe03de

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT

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
theorem _root_.solution {K : Type} [Field K] {r : ℕ} (c : K →+* K) (m : ℕ) (g : Fin r → K)
    (x y : Fin r → K) :
    formM c (wittMat r m g) x y = ∑ a, c (x a) * (wVal r m g a * y (wPart r m a)) := by
  unfold formM
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  have ha := a.isLt
  by_cases h : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m
  · have hw : wVal r m g a = 1 := if_pos h
    have hp : wPart r m a = Fin.rev a := if_pos h
    rw [hw, hp, one_mul, Finset.sum_eq_single (Fin.rev a)]
    · rw [wittMat, Matrix.of_apply, if_pos, one_mul]
      rw [Fin.val_rev]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, h2, h3⟩
        omega
      · rintro ⟨h1, -⟩
        apply hj
        ext
        rw [Fin.val_rev]
        omega
    · simp
  · have hw : wVal r m g a = g a := if_neg h
    have hp : wPart r m a = a := if_neg h
    rw [hw, hp, Finset.sum_eq_single a]
    · rw [wittMat, Matrix.of_apply, if_neg, if_pos ⟨rfl, by omega, by omega⟩]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, -⟩
        exact hj rfl
      · have hj' := j.isLt
        omega
    · simp
end ReciprocityTheory.MultiplicativeHeights.SemiPt

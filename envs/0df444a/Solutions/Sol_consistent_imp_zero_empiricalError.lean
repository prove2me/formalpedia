-- Prove2me | solution 1 for consistent_imp_zero_empiricalError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:20.219875+00:00
-- url     : https://prove2.me/submissions/50d5856a-07e7-47f4-928c-ca5119b09379

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (h : Concept X Bool) (c : Concept X Bool)
    {m : ℕ} (hm : 0 < m) (xs : Fin m → X)
    (hcons : IsConsistentWith X Bool h (fun i => (xs i, c (xs i)))) :
    EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool) = 0 := by
  have hm' : m ≠ 0 := by omega
  unfold EmpiricalError
  rw [if_neg hm']
  have hsum : (Finset.univ.sum fun i : Fin m =>
      zeroOneLoss Bool (h ((fun i => (xs i, c (xs i))) i).1)
        ((fun i => (xs i, c (xs i))) i).2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only
    unfold zeroOneLoss
    rw [if_pos (hcons i)]
  rw [hsum, zero_div]

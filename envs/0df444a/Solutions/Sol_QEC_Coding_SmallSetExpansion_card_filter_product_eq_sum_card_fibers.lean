-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.card_filter_product_eq_sum_card_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:42.221148+00:00
-- url     : https://prove2.me/submissions/16c93b36-e59e-4cd4-9cc4-6c3f7baf2736

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    {A B X U : Type*} [Fintype A] [Fintype B] [Fintype X]
    [DecidableEq X] [DecidableEq U]
    (f : A → X) (g : X → B → U) (u : U) :
    (Finset.univ.filter fun p : A × B => g (f p.1) p.2 = u).card =
      ∑ x, (Finset.univ.filter fun a : A => f a = x).card *
        (Finset.univ.filter fun b : B => g x b = u).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ p ∈ (Finset.univ : Finset A) ×ˢ (Finset.univ : Finset B),
    if g (f p.1) p.2 = u then 1 else 0) = _
  rw [Finset.sum_product]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset A) f
    (fun a => ∑ b ∈ (Finset.univ : Finset B),
      if g (f a) b = u then 1 else 0)]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_filter]
  simp only [Finset.mem_filter] at ha
  simp [ha.2]
end QEC.Coding.SmallSetExpansion

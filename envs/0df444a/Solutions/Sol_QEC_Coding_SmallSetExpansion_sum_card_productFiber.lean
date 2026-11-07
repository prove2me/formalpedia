-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_card_productFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:26.743879+00:00
-- url     : https://prove2.me/submissions/003a928a-8abb-4a8e-9ccb-3fd0b143089c

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (S : Finset (I × V)) :
    ∑ i, (productFiber S i).card = S.card := by
  classical
  calc
    ∑ i, (productFiber S i).card =
        ∑ i, (S.filter fun iv => iv.1 = i).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [productFiber, Finset.card_image_iff.mpr]
      intro x hx y hy hxy
      exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
        (Finset.mem_filter.mp hy).2.symm) hxy
    _ = S.card := by
      have hMaps : Set.MapsTo (fun x : I × V => x.1) (↑S)
          (↑(Finset.univ : Finset I)) := by
        intro x _hx
        exact Finset.mem_univ x.1
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (s := S) (t := (Finset.univ : Finset I))
          (f := fun x : I × V => x.1)
          hMaps).symm
end QEC.Coding.SmallSetExpansion

-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.card_productFiber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:27.64793+00:00
-- url     : https://prove2.me/submissions/cc33ae64-019d-4e56-8059-6d7dd79cf78b

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    {I : Type*} [DecidableEq I] [DecidableEq V]
    (S : Finset (I × V)) (i : I) :
    (productFiber S i).card ≤ S.card := by
  classical
  rw [productFiber, Finset.card_image_iff.mpr]
  · exact Finset.card_filter_le _ _
  · intro x hx y hy hxy
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm) hxy
end QEC.Coding.SmallSetExpansion

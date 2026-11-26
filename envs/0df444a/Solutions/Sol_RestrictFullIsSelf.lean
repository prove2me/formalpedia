-- Prove2me | solution 1 for RestrictFullIsSelf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:28.161623+00:00
-- url     : https://prove2.me/submissions/c4f9c8ad-82c9-4bca-bf43-64e4a5592607

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_RestrictFullIsSelf

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (A : Curve E) :
    curveRestrict A 0 A.len (le_refl 0) A.len_nonneg (le_refl A.len) = A := by
-- BODY
  have hfun : (fun u => A.toFun (0 + min (A.len - 0) (max 0 u))) = A.toFun := by
    funext u
    show A.toFun (0 + min (A.len - 0) (max 0 u)) = A.toFun u
    rw [zero_add, sub_zero]
    exact (A.clamped u).symm
  cases A with
  | mk len hnn f hcl hus =>
    simp only [curveRestrict, sub_zero] at *
    congr 1

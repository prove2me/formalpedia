-- Prove2me | solution 1 for OrderClosures.gaoIterationProduct_abs_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:17.919942+00:00
-- url     : https://prove2.me/submissions/dafb07cd-313f-4662-8c11-2c463c6f95cd

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ) (β : GaoComponentIndex κ) :
    |x|.1 β = |x.1 β| := rfl
end OrderClosures

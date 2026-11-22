-- Prove2me | solution 1 for OrderClosures.gaoIterationProduct_abs_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:06.10352+00:00
-- url     : https://prove2.me/submissions/ceffd7c4-ab09-4923-bd28-c7e9e9e15d7a

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
    (κ : Cardinal.{u}) (x : GaoIterationProduct κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) :
    |x|.2 a = |x.2 a| := rfl
end OrderClosures

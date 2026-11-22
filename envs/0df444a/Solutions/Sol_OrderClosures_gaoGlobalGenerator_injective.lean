-- Prove2me | solution 1 for OrderClosures.gaoGlobalGenerator_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:28.709618+00:00
-- url     : https://prove2.me/submissions/834ace63-e86f-44e2-959e-a3bda87a9588

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_gaoGlobalGenerator_index_eq_of_abs_le

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    Function.Injective (gaoGlobalGenerator κ hκ) := by
  intro a b hab
  apply gaoGlobalGenerator_index_eq_of_abs_le κ hκ
  rw [hab]
end OrderClosures

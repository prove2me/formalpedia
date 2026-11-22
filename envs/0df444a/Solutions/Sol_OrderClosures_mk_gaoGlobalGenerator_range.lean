-- Prove2me | solution 1 for OrderClosures.mk_gaoGlobalGenerator_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:59.062873+00:00
-- url     : https://prove2.me/submissions/033cf0fc-3de7-4e80-a76b-07aa4680b22f

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_gaoGlobalGenerator_injective

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)) =
      Cardinal.lift.{u + 1, u} κ := by
  calc
    Cardinal.mk (Set.range (gaoGlobalGenerator κ hκ)) =
        Cardinal.mk (ULift.{u + 1, u} (Cardinal.ord κ).ToType) :=
      Cardinal.mk_range_eq _ (gaoGlobalGenerator_injective κ hκ)
    _ = Cardinal.lift.{u + 1, u} κ := by
      change Cardinal.lift.{u + 1, u}
        (Cardinal.mk (Cardinal.ord κ).ToType) = Cardinal.lift.{u + 1, u} κ
      rw [Cardinal.mk_ord_toType]
end OrderClosures

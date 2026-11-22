-- Prove2me | solution 1 for OrderClosures.orderAdherence_gaoStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:02.166809+00:00
-- url     : https://prove2.me/submissions/01b166a5-52c9-4450-b3ce-7f7679315993

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Theorems.Thm_OrderClosures_orderAdherence_gaoStage_subset
public import Theorems.Thm_OrderClosures_gaoStage_succ_subset_orderAdherence

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    orderAdherence (GaoStageSet ξ γ) = GaoStageSet ξ (γ + 1) :=
  Set.Subset.antisymm (orderAdherence_gaoStage_subset ξ γ)
    (gaoStage_succ_subset_orderAdherence ξ γ hγ)
end OrderClosures

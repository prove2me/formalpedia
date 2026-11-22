-- Prove2me | solution 1 for OrderClosures.isSolid_gaoStageSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:10.164192+00:00
-- url     : https://prove2.me/submissions/d6313992-9801-4b59-97bc-01cd5c75f12b

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution (ξ β : Ordinal.{u}) :
    LatticeOrderedAddCommGroup.IsSolid (GaoStageSet ξ β) := by
  intro f hf g hgf
  obtain ⟨ζ, hζ, hfζ⟩ := hf
  exact ⟨ζ, hζ, hgf.trans hfζ⟩
end OrderClosures

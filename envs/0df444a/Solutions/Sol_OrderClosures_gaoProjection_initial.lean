-- Prove2me | solution 1 for OrderClosures.gaoProjection_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:58.593023+00:00
-- url     : https://prove2.me/submissions/3e04ec34-6cfe-467a-99da-374811c22d18

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_gaoComponentGenerator_mem
public import Theorems.Thm_OrderClosures_isSolid_gaoStageSet


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) :
    gaoProductProjection κ β '' gaoIterationSet κ hκ ⊆ GaoStageSet β.1 1 := by
  rintro _ ⟨x, ⟨g, ⟨a, rfl⟩, hx⟩, rfl⟩
  apply isSolid_gaoStageSet β.1 1 (gaoComponentGenerator_mem κ hκ β a)
  exact hx.1 β
end OrderClosures

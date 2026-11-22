-- Prove2me | solution 1 for OrderClosures.gaoProductProjection_orderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:31.171299+00:00
-- url     : https://prove2.me/submissions/69654c18-934f-4ca6-80d5-a193773f01c2

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_orderConvergesTo_gaoProductProjection

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoIterationProduct κ)) :
    gaoProductProjection κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductProjection κ β '' A) := by
  rintro _ ⟨x, ⟨i, hpre, hdir, hne, f, hfA, hfx⟩, rfl⟩
  exact ⟨i, hpre, hdir, hne, fun j ↦ gaoProductProjection κ β (f j),
    fun j ↦ ⟨f j, hfA j, rfl⟩, orderConvergesTo_gaoProductProjection κ β hfx⟩
end OrderClosures

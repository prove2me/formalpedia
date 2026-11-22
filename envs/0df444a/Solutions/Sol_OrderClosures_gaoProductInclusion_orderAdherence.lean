-- Prove2me | solution 1 for OrderClosures.gaoProductInclusion_orderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:47.268693+00:00
-- url     : https://prove2.me/submissions/3aec5a16-c18d-4499-8a19-b95e555e5ae3

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_orderConvergesTo_gaoProductInclusion

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ) (A : Set (GaoComponent β.1)) :
    gaoProductInclusion κ β '' orderAdherence A ⊆
      orderAdherence (gaoProductInclusion κ β '' A) := by
  rintro _ ⟨x, ⟨i, hpre, hdir, hne, f, hfA, hfx⟩, rfl⟩
  exact ⟨i, hpre, hdir, hne, fun j ↦ gaoProductInclusion κ β (f j),
    fun j ↦ ⟨f j, hfA j, rfl⟩, orderConvergesTo_gaoProductInclusion κ β hfx⟩
end OrderClosures

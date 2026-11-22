-- Prove2me | solution 1 for OrderClosures.gaoComponentGenerator_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:22.530704+00:00
-- url     : https://prove2.me/submissions/7945a0e6-1f14-4f19-891f-9dea53c0cca9

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
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) (ζ : GaoSuccessorGenerator β.1) :
    gaoComponentGenerator κ hκ β
        (gaoGeneratorEmbedding κ hκ β.1 β.2 ζ) =
      ordinalProjection β.1 ζ.1 := by
  rw [gaoComponentGenerator, dif_pos ⟨ζ, rfl⟩]
  congr 1
  exact congrArg (fun η : GaoSuccessorGenerator β.1 ↦ η.1)
    ((gaoGeneratorEmbedding κ hκ β.1 β.2).injective
      (Classical.choose_spec
        (show ∃ η : GaoSuccessorGenerator β.1,
            gaoGeneratorEmbedding κ hκ β.1 β.2 η =
              gaoGeneratorEmbedding κ hκ β.1 β.2 ζ from ⟨ζ, rfl⟩)))
end OrderClosures

-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.mem_generatorImage_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:54.233847+00:00
-- url     : https://prove2.me/submissions/0f57376b-86e0-48bd-8899-b93390a664fd

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (g : Matrix R W F) (c : Word F W) :
    c ∈ generatorImage g ↔
      ∃ a : Word F R, g.transpose.mulVec a = c := by
  classical
  unfold generatorImage
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Matrix.toLin'_apply]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Matrix.toLin'_apply]⟩
end QEC.Coding.ProductExpansion

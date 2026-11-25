-- Prove2me | solution 1 for SNumbers.ne_top_of_rank_le_of_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:18:03.195815+00:00
-- url     : https://prove2.me/submissions/54608915-dab8-46a8-95ef-7c7d431931d3

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {n : ℕ}
namespace SNumbers
theorem _root_.solution {V : Submodule 𝕜 X}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    V ≠ ⊤ := by
  rintro rfl
  rw [rank_top] at hV
  exact absurd (hV.trans_lt h) (lt_irrefl _)
end SNumbers

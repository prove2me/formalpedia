-- Prove2me | solution 1 for SNumbers.ne_bot_of_rank_quotient_le_of_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:58.838996+00:00
-- url     : https://prove2.me/submissions/a601eb06-4ae4-4f85-9bd1-e3dd0e72b38d

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
theorem _root_.solution {M : Submodule 𝕜 X}
    (hM : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    M ≠ ⊥ := by
  rintro rfl
  rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule 𝕜 X) rfl).rank_eq] at hM
  exact absurd (hM.trans_lt h) (lt_irrefl _)
end SNumbers

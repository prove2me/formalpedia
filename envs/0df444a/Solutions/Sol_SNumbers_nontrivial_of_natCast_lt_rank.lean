-- Prove2me | solution 1 for SNumbers.nontrivial_of_natCast_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:08:38.907559+00:00
-- url     : https://prove2.me/submissions/f0f5c812-197f-4d2b-bc42-5bee07a6239d

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
theorem _root_.solution (h : (n : Cardinal) < Module.rank 𝕜 X) :
    Nontrivial X :=
  rank_pos_iff_nontrivial.mp ((zero_le : (0 : Cardinal) ≤ n).trans_lt h)
end SNumbers

-- Prove2me | solution 1 for SNumbers.finiteDimensional_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:50.859057+00:00
-- url     : https://prove2.me/submissions/95744062-a05c-42c2-9242-258c183a5cf5

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
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) : FiniteDimensional 𝕜 V :=
  Module.rank_lt_aleph0_iff.mp (hV.trans_lt (Cardinal.natCast_lt_aleph0))
end SNumbers

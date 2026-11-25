-- Prove2me | solution 1 for SNumbers.IsSNumberSequence.le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:54.565693+00:00
-- url     : https://prove2.me/submissions/ceeaad0f-676e-4529-8279-eb9f5df5de1f

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
namespace SNumbers
namespace IsSNumberSequence
theorem _root_.solution {s : Family 𝕜} (h : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (h.antitone S) (Nat.zero_le n)).trans_eq (h.norm_at_zero S)
end IsSNumberSequence
end SNumbers

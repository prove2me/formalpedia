-- Prove2me | solution 1 for SNumbers.Additive.subadditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:51:55.53414+00:00
-- url     : https://prove2.me/submissions/999add55-cfc7-473f-a142-47044b1d6de2

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
namespace Additive
theorem _root_.solution {s : Family 𝕜} (h : Additive s) (h0 : NormAtZero s) :
    Subadditive s := by
  intro X Y _ _ _ _ S T n
  have h' := h S T n 0
  rwa [Nat.add_zero, h0 T] at h'
end Additive
end SNumbers

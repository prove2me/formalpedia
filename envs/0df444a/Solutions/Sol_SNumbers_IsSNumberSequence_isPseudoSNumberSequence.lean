-- Prove2me | solution 1 for SNumbers.IsSNumberSequence.isPseudoSNumberSequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:10.632905+00:00
-- url     : https://prove2.me/submissions/e0add3a0-ac11-42ec-9079-84a79294b903

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
theorem _root_.solution {s : Family 𝕜} (h : IsSNumberSequence s) :
    IsPseudoSNumberSequence s :=
  ⟨h.nonneg, h.norm_at_zero, h.antitone, h.subadditive, h.ideal⟩
end IsSNumberSequence
end SNumbers

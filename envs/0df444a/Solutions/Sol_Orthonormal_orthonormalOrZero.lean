-- Prove2me | solution 1 for Orthonormal.orthonormalOrZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:41:42.059487+00:00
-- url     : https://prove2.me/submissions/9829aa31-83a0-4ba5-a0da-4c54d8d59e77

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
namespace SVD
namespace _root_.Orthonormal
theorem _root_.solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ι : Type*} {u : ι → H} (hu : Orthonormal 𝕜 u) :
    OrthonormalOrZero 𝕜 u :=
  ⟨fun i => Or.inl (hu.1 i), fun _ _ hij => hu.2 hij⟩
end _root_.Orthonormal
end SVD

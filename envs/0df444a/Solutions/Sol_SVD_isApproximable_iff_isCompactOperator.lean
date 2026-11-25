-- Prove2me | solution 1 for SVD.isApproximable_iff_isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:25:25.151853+00:00
-- url     : https://prove2.me/submissions/d0202d99-5f80-428e-85a0-b0472cef5fb4

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SVD_IsCompactOperator_isApproximable
public import Theorems.Thm_SVD_IsApproximable_isCompactOperator


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
theorem _root_.solution (S : H₁ →L[𝕜] H₂) :
    IsApproximable S ↔ IsCompactOperator S :=
  ⟨IsApproximable.isCompactOperator, IsCompactOperator.isApproximable⟩
end SVD

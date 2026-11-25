-- Prove2me | solution 1 for SVD.isCompactOperator_iff_tendsto_bernsteinNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:55:36.864214+00:00
-- url     : https://prove2.me/submissions/830ad7e8-5d0c-4845-bd74-da0c0baaa313

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SVD_isCompactOperator_iff_tendsto_sn
public import Theorems.Thm_SNumbers_isSNumberSequence_bernsteinNumber


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
    IsCompactOperator S ↔ Tendsto (SNumbers.bernsteinNumber S) atTop (𝓝 0) :=
  isCompactOperator_iff_tendsto_sn SNumbers.isSNumberSequence_bernsteinNumber S
end SVD

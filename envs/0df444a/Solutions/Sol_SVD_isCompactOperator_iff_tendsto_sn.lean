-- Prove2me | solution 1 for SVD.isCompactOperator_iff_tendsto_sn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:26:56.567514+00:00
-- url     : https://prove2.me/submissions/c1516d4c-8367-4d9f-87a9-18afe4eabd45

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SVD_isApproximable_iff_isCompactOperator
public import Theorems.Thm_SNumbers_allSNumbers_eq_on_HilbertSpace


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
theorem _root_.solution {s : SNumbers.Family 𝕜}
    (hs : SNumbers.IsSNumberSequence s) (S : H₁ →L[𝕜] H₂) :
    IsCompactOperator S ↔ Tendsto (fun n => s S n) atTop (𝓝 0) :=
  (isApproximable_iff_isCompactOperator S).symm.trans
    (Filter.tendsto_congr fun n =>
      SNumbers.allSNumbers_eq_on_HilbertSpace hs S n).symm
end SVD

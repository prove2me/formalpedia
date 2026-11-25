-- Prove2me | solution 1 for SVD.IsCompactOperator.isApproximable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:24:14.4458+00:00
-- url     : https://prove2.me/submissions/700ddbeb-9ea3-4a90-ac05-d3458af9be85

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SVD_svd_sigma_eq_approx


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
namespace IsCompactOperator
theorem _root_.solution {S : H₁ →L[𝕜] H₂}
    (hS : IsCompactOperator S) :
    IsApproximable S := by
  obtain ⟨σ, u, v, hσ0, hσanti, hu, hv, hut, hvt, hσlim, hsum⟩ := IsCompactOperator.SVD hS
  exact (Filter.tendsto_congr fun n =>
    (svd_sigma_eq_approx hσ0 hσanti hu hv hut hvt hsum n).symm).mpr hσlim
end IsCompactOperator
end SVD

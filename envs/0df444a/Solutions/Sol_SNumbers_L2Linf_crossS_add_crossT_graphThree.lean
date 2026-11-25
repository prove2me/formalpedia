-- Prove2me | solution 1 for SNumbers.L2Linf.crossS_add_crossT_graphThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:15.739353+00:00
-- url     : https://prove2.me/submissions/aa87c309-9f3c-4bc6-92e0-8fa75cc06e42

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.idEmbed_apply
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution (x : PiLp 2 (fun _ : Fin 71 => 𝕜)) :
    (crossS + crossT : L2LinfProd 𝕜 →L[𝕜] L2LinfProd 𝕜) (graphThree x) =
      (3 : 𝕜)⁻¹ • graphThree x := by
  refine Prod.ext ?_ ?_
  · ext i
    simp [crossS, crossT, graphThree]
    ring
  · ext i
    simp [crossS, crossT, graphThree]
end SNumbers.L2Linf

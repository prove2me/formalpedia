-- Prove2me | solution 1 for SNumbers.prod_approximationNumber_eq_norm_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:24:45.421327+00:00
-- url     : https://prove2.me/submissions/44944ade-2452-41f3-9539-5ae772f1a151

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
public import Theorems.Thm_SNumbers_isSNumberSequence_approximationNumber
public import Theorems.Thm_SNumbers_sn_eq_singularValues_of_finiteDimensional


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Nontrivial E] (T : E →L[𝕜] E) :
    ∏ k ∈ Finset.range (Module.finrank 𝕜 E), approximationNumber T k
      = ‖LinearMap.det (T : E →ₗ[𝕜] E)‖ := by
  rw [← LinearMap.normDet_eq_norm_det, LinearMap.normDet_eq_prod_singularValues]
  exact Finset.prod_congr rfl fun k _ =>
    sn_eq_singularValues_of_finiteDimensional isSNumberSequence_approximationNumber T k
end SNumbers

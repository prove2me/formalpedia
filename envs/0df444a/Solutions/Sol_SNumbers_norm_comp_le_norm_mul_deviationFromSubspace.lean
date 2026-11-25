-- Prove2me | solution 1 for SNumbers.norm_comp_le_norm_mul_deviationFromSubspace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:17:21.951496+00:00
-- url     : https://prove2.me/submissions/dbe03255-6b11-4f2e-944e-61df4edc052d

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
public import Theorems.Thm_Submodule_liftQL_mkQL
public import Theorems.Thm_Submodule_norm_liftQL_le
attribute [local simp] Submodule.liftQL_mkQL



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
omit [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y}
    {V : Submodule 𝕜 Y} {R : Y →L[𝕜] Y}
    (hR : V ≤ LinearMap.ker (R : Y →ₗ[𝕜] Y)) :
    ‖R.comp S‖ ≤ ‖R‖ * deviationFromSubspace S V := by
  -- `R = (V.liftQL R hR) ∘ π_V`, so `R ∘ S = (V.liftQL R hR) ∘ (π_V ∘ S)`.
  have hfac : R.comp S = (V.liftQL R hR).comp (V.mkQL.comp S) := by
    ext x
    show R (S x) = V.liftQL R hR (V.mkQL (S x))
    rw [Submodule.liftQL_mkQL]
  rw [hfac]
  calc ‖(V.liftQL R hR).comp (V.mkQL.comp S)‖
      ≤ ‖V.liftQL R hR‖ * ‖V.mkQL.comp S‖ := opNorm_comp_le _ _
    _ ≤ ‖R‖ * ‖V.mkQL.comp S‖ :=
        mul_le_mul_of_nonneg_right (V.norm_liftQL_le R hR) (norm_nonneg _)
    _ = ‖R‖ * deviationFromSubspace S V := rfl
end SNumbers

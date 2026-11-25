-- Prove2me | solution 1 for SNumbers.deviationFromSubspace_comp_sup_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:00:36.701095+00:00
-- url     : https://prove2.me/submissions/046ef0e9-def1-4384-b5ef-940e7dfbf6b4

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_deviationFromSubspace_anti
public import Theorems.Thm_Submodule_liftQL_mkQL
public import Theorems.Thm_Submodule_norm_liftQL_le
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y)
    (V : Submodule 𝕜 Z) (U : Submodule 𝕜 Y) :
    deviationFromSubspace (S.comp T) (V ⊔ U.map (S : Y →ₗ[𝕜] Z)) ≤
      deviationFromSubspace S V * deviationFromSubspace T U := by
  set L : Submodule 𝕜 Z := V ⊔ U.map (S : Y →ₗ[𝕜] Z) with hL
  set SL : Y →L[𝕜] Z ⧸ L := L.mkQL.comp S with hSL
  -- `y ↦ [S y]_L` vanishes on `U`, since `S(U) ⊆ L`
  have h_ker : U ≤ LinearMap.ker (SL : Y →ₗ[𝕜] Z ⧸ L) := by
    intro w hw
    show L.mkQL (S w) = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (le_sup_right : U.map (S : Y →ₗ[𝕜] Z) ≤ L) (Submodule.mem_map_of_mem hw)
  -- and its norm is at most `‖π_V ∘ S‖`, since `V ≤ L`
  have h_SL : ‖SL‖ ≤ deviationFromSubspace S V :=
    deviationFromSubspace_anti S (le_sup_left : V ≤ L)
  have hfac : L.mkQL.comp (S.comp T) = (U.liftQL SL h_ker).comp (U.mkQL.comp T) := by
    ext x
    exact (U.liftQL_mkQL SL h_ker (T x)).symm
  show ‖L.mkQL.comp (S.comp T)‖ ≤ _
  rw [hfac]
  calc ‖(U.liftQL SL h_ker).comp (U.mkQL.comp T)‖
      ≤ ‖U.liftQL SL h_ker‖ * ‖U.mkQL.comp T‖ := opNorm_comp_le _ _
    _ ≤ deviationFromSubspace S V * deviationFromSubspace T U :=
        mul_le_mul_of_nonneg_right ((U.norm_liftQL_le SL h_ker).trans h_SL) (norm_nonneg _)
end SNumbers

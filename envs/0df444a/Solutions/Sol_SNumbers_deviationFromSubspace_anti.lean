-- Prove2me | solution 1 for SNumbers.deviationFromSubspace_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:21.372811+00:00
-- url     : https://prove2.me/submissions/7acf1332-0dc5-4c84-80b2-c0cc823dd813

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_Submodule_liftQL_mkQL
public import Theorems.Thm_Submodule_norm_liftQL_le
public import Theorems.Thm_Submodule_norm_mkQL_le
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
theorem _root_.solution (S : X →L[𝕜] Y) {V V' : Submodule 𝕜 Y} (h : V ≤ V') :
    deviationFromSubspace S V' ≤ deviationFromSubspace S V := by
  -- `π_{V'}` vanishes on `V`, so it descends to `Y/V`
  have h_ker : V ≤ LinearMap.ker (V'.mkQL : Y →ₗ[𝕜] Y ⧸ V') := by
    intro v hv
    show V'.mkQL v = 0
    rw [Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h hv
  have hfac : V'.mkQL.comp S = (V.liftQL V'.mkQL h_ker).comp (V.mkQL.comp S) := by
    ext x
    exact (V.liftQL_mkQL V'.mkQL h_ker (S x)).symm
  show ‖V'.mkQL.comp S‖ ≤ ‖V.mkQL.comp S‖
  rw [hfac]
  calc ‖(V.liftQL V'.mkQL h_ker).comp (V.mkQL.comp S)‖
      ≤ ‖V.liftQL V'.mkQL h_ker‖ * ‖V.mkQL.comp S‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖V.mkQL.comp S‖ :=
        mul_le_mul_of_nonneg_right ((V.norm_liftQL_le _ h_ker).trans V'.norm_mkQL_le)
          (norm_nonneg _)
    _ = ‖V.mkQL.comp S‖ := one_mul _
end SNumbers

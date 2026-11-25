-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_eq_zero_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:59.434911+00:00
-- url     : https://prove2.me/submissions/fda5120b-d908-4939-813c-1fe7aea36320

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
public import Theorems.Thm_SNumbers_kolmogorovNumber_nonneg
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    kolmogorovNumber S n = 0 := by
  refine le_antisymm ?_ (kolmogorovNumber_nonneg S n)
  -- Take `V = range S`. Then `V.mkQL ∘ S = 0`, so `deviation = 0`.
  set V : Submodule 𝕜 Y := LinearMap.range (S : X →ₗ[𝕜] Y) with hV_def
  have hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal) := hS
  refine (kolmogorovNumber_le_deviation hV_rank).trans ?_
  -- `V.mkQL.comp S = 0` because every `S x ∈ V`, so `[S x] = 0` in `Y/V`.
  have h_comp_zero : V.mkQL.comp S = 0 := by
    ext x
    simp only [coe_comp, Function.comp_apply, zero_apply,
      Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self (S : X →ₗ[𝕜] Y) x
  show ‖V.mkQL.comp S‖ ≤ 0
  rw [h_comp_zero]; exact le_of_eq (ContinuousLinearMap.opNorm_zero)
end SNumbers

-- Prove2me | solution 1 for SNumbers.gelfandNumber_eq_zero_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:07.490779+00:00
-- url     : https://prove2.me/submissions/23154261-5a7a-4dd9-94c5-01c909e98d28

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandNumber_le_deviation
public import Theorems.Thm_SNumbers_gelfandNumber_nonneg
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero



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
    gelfandNumber S n = 0 := by
  refine le_antisymm ?_ (gelfandNumber_nonneg S n)
  -- Take `M = ker S`. Then `S.comp M.subtypeL = 0`, so `deviation = 0`.
  set M : Submodule 𝕜 X := LinearMap.ker (S : X →ₗ[𝕜] Y) with hM_def
  -- (a) `M` is closed, since `S` is continuous and `{0}` is closed.
  have hM_closed : IsClosed (M : Set X) := by
    have h_eq : (M : Set X) = S ⁻¹' ({0} : Set Y) := by
      ext x
      simp [hM_def, LinearMap.mem_ker]
    rw [h_eq]
    exact isClosed_singleton.preimage S.continuous
  -- (b) `codim M = rank S ≤ n` via the first iso `X ⧸ ker S ≃ range S`.
  have hM_rank : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) := by
    calc Module.rank 𝕜 (X ⧸ M)
        = Module.rank 𝕜 (LinearMap.range (S : X →ₗ[𝕜] Y)) :=
          (LinearMap.quotKerEquivRange (S : X →ₗ[𝕜] Y)).rank_eq
      _ ≤ (n : Cardinal) := hS
  refine (gelfandNumber_le_deviation hM_closed hM_rank).trans ?_
  -- (c) `S.comp M.subtypeL = 0`: every `x ∈ M = ker S` has `S x = 0`.
  have h_comp_zero : S.comp M.subtypeL = 0 := by
    ext x
    simp only [coe_comp, Function.comp_apply, zero_apply,
      Submodule.subtypeL_apply]
    exact x.2
  show ‖S.comp M.subtypeL‖ ≤ 0
  rw [h_comp_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero
end SNumbers

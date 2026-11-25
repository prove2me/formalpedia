-- Prove2me | solution 1 for SNumbers.approximationNumber_comp_le_norm_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:21.710628+00:00
-- url     : https://prove2.me/submissions/4522484b-f552-4f07-af7d-0a3ddf90cb19

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero


attribute [local simp] SNumbers.approximationNumber_zero_eq_norm

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
theorem _root_.solution {S L : Y →L[𝕜] Z} {T K : X →L[𝕜] Y}
    {n m : ℕ} (hL : L.rank ≤ (n : Cardinal)) (hK : K.rank ≤ (m : Cardinal)) :
    approximationNumber (S.comp T) (n + m) ≤ ‖S - L‖ * ‖T - K‖ := by
  set R : X →L[𝕜] Z := L.comp T + (S - L).comp K with hR
  -- `rank R ≤ rank (L ∘ T) + rank ((S - L) ∘ K) ≤ rank L + rank K ≤ n + m`
  have h_rank : R.rank ≤ ((n + m : ℕ) : Cardinal) := by
    rw [Nat.cast_add]
    calc R.rank
        ≤ (L.comp T).rank + ((S - L).comp K).rank :=
          LinearMap.rank_add_le ((L.comp T : X →L[𝕜] Z) : X →ₗ[𝕜] Z)
            ((S - L).comp K : X →ₗ[𝕜] Z)
      _ ≤ L.rank + K.rank :=
          add_le_add (LinearMap.rank_comp_le_left (T : X →ₗ[𝕜] Y) (L : Y →ₗ[𝕜] Z))
            (LinearMap.rank_comp_le_right (K : X →ₗ[𝕜] Y) ((S - L : Y →L[𝕜] Z) : Y →ₗ[𝕜] Z))
      _ ≤ n + m := add_le_add hL hK
  -- the residual factors
  have h_eq : S.comp T - R = (S - L).comp (T - K) := by
    rw [hR]
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  calc approximationNumber (S.comp T) (n + m)
      ≤ ‖S.comp T - R‖ := approximationNumber_le_norm_sub h_rank
    _ = ‖(S - L).comp (T - K)‖ := by rw [h_eq]
    _ ≤ ‖S - L‖ * ‖T - K‖ := opNorm_comp_le _ _
end SNumbers

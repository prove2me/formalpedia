-- Prove2me | solution 1 for SNumbers.approximationNumber_add_le_norm_sub_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:45.930133+00:00
-- url     : https://prove2.me/submissions/0772b2a4-41e3-488b-9016-426c526269e1

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub

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
theorem _root_.solution {S T L K : X →L[𝕜] Y} {n m : ℕ}
    (hL : L.rank ≤ (n : Cardinal)) (hK : K.rank ≤ (m : Cardinal)) :
    approximationNumber (S + T) (n + m) ≤ ‖S - L‖ + ‖T - K‖ := by
  -- `rank (L + K) ≤ rank L + rank K ≤ n + m`
  have h_rank : (L + K).rank ≤ ((n + m : ℕ) : Cardinal) := by
    rw [Nat.cast_add]
    exact (LinearMap.rank_add_le (L : X →ₗ[𝕜] Y) (K : X →ₗ[𝕜] Y)).trans (add_le_add hL hK)
  calc approximationNumber (S + T) (n + m)
      ≤ ‖(S + T) - (L + K)‖ := approximationNumber_le_norm_sub h_rank
    _ = ‖(S - L) + (T - K)‖ := by congr 1; abel
    _ ≤ ‖S - L‖ + ‖T - K‖ := norm_add_le _ _
end SNumbers

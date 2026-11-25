-- Prove2me | solution 1 for SNumbers.IsMetricSurjection.norm_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:17.035099+00:00
-- url     : https://prove2.me/submissions/a89e18d1-2714-4575-ac50-472a23483d61

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
public import Theorems.Thm_SNumbers_IsMetricInjection_norm_le_one

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
namespace IsMetricSurjection
theorem _root_.solution {Q : W →L[𝕜] X} (hQ : IsMetricSurjection Q)
    (T : X →L[𝕜] Y) : ‖T.comp Q‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · -- `‖T ∘ Q‖ ≤ ‖T‖ ‖Q‖ ≤ ‖T‖`.
    calc ‖T.comp Q‖
        ≤ ‖T‖ * ‖Q‖ := opNorm_comp_le _ _
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hQ.norm_le_one (norm_nonneg _)
      _ = ‖T‖ := mul_one _
  · -- `‖T x‖ ≤ ‖T ∘ Q‖ ‖x‖`: lift `x` to `w` with `‖w‖ ≈ ‖x‖`, then
    -- `‖T x‖ = ‖(T ∘ Q) w‖ ≤ ‖T ∘ Q‖ ‖w‖`, and let `ε → 0`.
    refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : (0 : ℝ) < ‖T.comp Q‖ + 1 := by positivity
    obtain ⟨w, hw, hwn⟩ := hQ.exists_preimage_lt x (ε / (‖T.comp Q‖ + 1)) (by positivity)
    calc ‖T x‖
        = ‖(T.comp Q) w‖ := by rw [ContinuousLinearMap.comp_apply, hw]
      _ ≤ ‖T.comp Q‖ * ‖w‖ := (T.comp Q).le_opNorm w
      _ ≤ ‖T.comp Q‖ * (‖x‖ + ε / (‖T.comp Q‖ + 1)) :=
          mul_le_mul_of_nonneg_left hwn.le (norm_nonneg (T.comp Q))
      _ = ‖T.comp Q‖ * ‖x‖ + ‖T.comp Q‖ / (‖T.comp Q‖ + 1) * ε := by ring
      _ ≤ ‖T.comp Q‖ * ‖x‖ + 1 * ε := by
          gcongr
          rw [div_le_one hpos]; linarith
      _ = ‖T.comp Q‖ * ‖x‖ + ε := by ring
end IsMetricSurjection
end SNumbers

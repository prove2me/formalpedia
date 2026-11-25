-- Prove2me | solution 1 for SNumbers.deviationFromSubspace_comp_metricSurjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:34.138143+00:00
-- url     : https://prove2.me/submissions/08e01f06-1941-4d13-8637-770b20c28fa6

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
theorem _root_.solution {Q : W →L[𝕜] X}
    (hQ : IsMetricSurjection Q) (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (S.comp Q) V = deviationFromSubspace S V := by
  show ‖V.mkQL.comp (S.comp Q)‖ = ‖V.mkQL.comp S‖
  rw [← ContinuousLinearMap.comp_assoc]
  -- Abstract `T := π_V ∘ S` as an opaque operator and inline
  -- `IsMetricSurjection.norm_comp` (goal `‖T.comp Q‖ = ‖T‖`).
  generalize V.mkQL.comp S = T
  refine le_antisymm ?_ ?_
  · calc ‖T.comp Q‖
        ≤ ‖T‖ * ‖Q‖ := opNorm_comp_le _ _
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hQ.norm_le_one (norm_nonneg T)
      _ = ‖T‖ := mul_one _
  · refine T.opNorm_le_bound (norm_nonneg (T.comp Q)) fun x => ?_
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
end SNumbers

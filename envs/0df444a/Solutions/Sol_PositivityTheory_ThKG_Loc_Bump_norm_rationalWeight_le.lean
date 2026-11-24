-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.norm_rationalWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:44.122421+00:00
-- url     : https://prove2.me/submissions/8b30746c-115a-4954-916e-7a83e288061d

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : ‖r0 κ e x‖ ≤ (1 + ‖x‖) ^ (2 * e * Fintype.card ι) := by
  rw [r0, norm_prod, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun w _ => ?_
  rw [norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real, norm_norm]
  have h1 : (‖x w‖ / ‖x w‖) ^ κ w ≤ 1 := pow_le_one₀ (by positivity) (div_self_le_one _)
  have h2 : ‖x w‖ ^ (2 * e) ≤ (1 + ‖x‖) ^ (2 * e) := pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_le_pi_norm x w]) _
  calc _ ≤ 1 * (1 + ‖x‖) ^ (2 * e) := by gcongr
    _ = _ := one_mul _
end PositivityTheory.ThKG.Loc.Bump

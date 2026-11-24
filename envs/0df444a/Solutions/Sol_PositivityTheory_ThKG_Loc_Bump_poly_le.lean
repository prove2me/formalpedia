-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.poly_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:10.590112+00:00
-- url     : https://prove2.me/submissions/aac69da3-2aef-4232-bae0-5b4fe36c8cb9

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian

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
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (t : ℝ) (ht : 0 ≤ t) (s : ℕ) : (1 + t) ^ s * Real.exp (-2 * Real.pi * t ^ 2) ≤ Real.exp (s ^ 2) := by
  have h1 : (1 + t) ^ s ≤ Real.exp (s * t) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) s
  calc _ ≤ Real.exp (s * t) * Real.exp (-2 * Real.pi * t ^ 2) := by gcongr
    _ ≤ _ := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      nlinarith [Real.pi_gt_three, sq_nonneg (t - s), sq_nonneg t, sq_nonneg (s : ℝ)]
end PositivityTheory.ThKG.Loc.Bump

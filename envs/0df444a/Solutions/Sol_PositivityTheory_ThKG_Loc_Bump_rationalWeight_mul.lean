-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.rationalWeight_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:04.610601+00:00
-- url     : https://prove2.me/submissions/731ed018-f113-473c-96ff-eed21841ff44

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (κ : ι → ℕ) (e : ℕ) (x y : ι → ℂ) : r0 κ e (x * y) = r0 κ e x * r0 κ e y := by
  rw [r0, r0, r0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp only [Pi.mul_apply, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_pow]; ring
end PositivityTheory.ThKG.Loc.Bump

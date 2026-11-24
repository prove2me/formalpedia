-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.rationalWeight_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:10.79391+00:00
-- url     : https://prove2.me/submissions/6c14ce76-3cfb-469d-8f43-d406a64c43a4

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
theorem _root_.solution (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) : r0 κ e x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => by have := hx w; simp [this]
end PositivityTheory.ThKG.Loc.Bump

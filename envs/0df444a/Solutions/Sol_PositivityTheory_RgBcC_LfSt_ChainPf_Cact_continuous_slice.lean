-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.continuous_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:07.320882+00:00
-- url     : https://prove2.me/submissions/33fb2592-d29d-406b-9960-c42e4f7d9a0f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Cact
variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
variable {O : Set H} {OZ : Set Z}
namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact
theorem _root_.solution {W : Type} [TopologicalSpace W] {Φ : H × Z → W} {ι : Γ → Z} (hιc : Continuous ι)
    (hι : ∀ y, ι y ∈ OZ) (hΦ : ContinuousOn Φ (O ×ˢ OZ)) {x : H} (hx : x ∈ O) :
    Continuous fun y : Γ => Φ (x, ι y) :=
  hΦ.comp_continuous (continuous_const.prodMk hιc) fun y => ⟨hx, hι y⟩
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact

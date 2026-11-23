-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.hasFDerivAt_pd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:00.754805+00:00
-- url     : https://prove2.me/submissions/b188eb4e-18f9-46c4-82f1-73afde51f701

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
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {x : H} {z : Z} (hx : x ∈ O)
    (hz : z ∈ OZ) : HasFDerivAt (fun x' => Φ (x', z)) (pd Φ (x, z)) x := by
  have hd : DifferentiableAt ℝ Φ (x, z) :=
    (hΦ.differentiableOn (by simp)).differentiableAt ((hO.prod hOZ).mem_nhds ⟨hx, hz⟩)
  exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z)
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact

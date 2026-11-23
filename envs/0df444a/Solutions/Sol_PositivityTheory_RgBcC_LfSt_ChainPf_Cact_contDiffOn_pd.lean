-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.contDiffOn_pd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:58.512801+00:00
-- url     : https://prove2.me/submissions/c28cf541-f47c-4333-b78f-41bbe094760b

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
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) : ContDiffOn ℝ ∞ (pd Φ) (O ×ˢ OZ) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) (O ×ˢ OZ) := hΦ.fderiv_of_isOpen (hO.prod hOZ) (by simp)
  exact h1.clm_comp contDiffOn_const
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
